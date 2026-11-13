import QOI.Fast.Impl

/-!
# `QOI.Fast.decodeRGBA` computes `QOI.Spec.decode`

One refinement step, by functional induction over `loop` (`loop_eq`, one case per branch of the
loop). The loop state is related to the arguments of `Spec.pixels`:

* input: position `pos` ↔ the remaining chunk bytes `rest b e pos = (b.data.toList.take e).drop pos`;
* index: `idx : Array UInt32` ↔ `I : Vector Pixel 64` by `idx.toList.map unpack = I.toList` (`IdxRel`);
* previous pixel: the four `UInt8` arguments ↔ `⟨pr, pg, pb, pa⟩`;
* pixels still to decode: `(oe - o) / 4`;
* run pattern: its first `4 * pl` bytes are `rgbaL (replicate pl (unpack pp))` (only needed to show
  that the `copySlice` of a long run writes the right bytes);
* output: `loop` returns the first `o` bytes of `out` followed by the RGBA bytes of the pixels the spec
  decodes from this state.

Per-chunk lemmas (`chunk_index`, `chunk_diff`, ...) evaluate `Spec.chunk` on a cons-list given the tag
range; `single_step`/`run_step`/`none_step` glue one loop step to one unfolding of `Spec.pixels`.
The header is handled by `decode_cons`, a closed form of `Spec.decode` on a 14-byte prefix.
-/

set_option linter.deprecated false
set_option linter.unusedSimpArgs false
namespace QOI.Fast
open QOI.Spec

/-! ## ByteArray / list plumbing -/

@[simp] theorem length_data_toList (a : ByteArray) : a.data.toList.length = a.size := by simp

theorem toList_loop (b : ByteArray) (i : Nat) (r : List UInt8) :
    ByteArray.toList.loop b i r = r.reverse ++ b.data.toList.drop i := by
  fun_induction ByteArray.toList.loop b i r with
  | case1 i r h ih =>
    rw [ih, List.reverse_cons, List.append_assoc]
    congr 1
    rw [List.drop_eq_getElem_cons (i := i) (by simpa using h)]
    simp only [List.singleton_append, List.cons.injEq, and_true]
    show b.data[i]! = _
    simp [getElem!_pos, h]
  | case2 i r h =>
    simp [List.drop_of_length_le (by simp; omega : b.data.toList.length ≤ i)]

theorem toList_eq (b : ByteArray) : b.toList = b.data.toList := by
  simp [ByteArray.toList, toList_loop]

theorem data_uset (a : ByteArray) (i : USize) (v : UInt8) (h) :
    (a.uset i v h).data = a.data.set i.toNat v h := rfl

theorem uget_eq (a : ByteArray) (i : USize) (h) :
    a.uget i h = a.data.toList[i.toNat]'(by simpa using h) := by
  simp [ByteArray.uget]

/-- Writing four consecutive bytes, then keeping everything up to them. -/
theorem take_set4 (l : List UInt8) (o : Nat) (r g b a : UInt8) (h : o + 4 ≤ l.length) :
    ((((l.set o r).set (o + 1) g).set (o + 2) b).set (o + 3) a).take (o + 4) =
      l.take o ++ [r, g, b, a] := by
  apply List.ext_getElem?
  intro j
  simp only [List.getElem?_take, List.getElem?_set, List.getElem?_append, List.length_set,
    List.length_take]
  have hm : min o l.length = o := Nat.min_eq_left (by omega)
  rw [hm]
  by_cases hj : j < o
  · simp [hj, show j < o + 4 by omega, show ¬o + 3 = j by omega, show ¬o + 2 = j by omega,
      show ¬o + 1 = j by omega, show ¬o = j by omega]
  · by_cases hj4 : j < o + 4
    · have : j = o ∨ j = o + 1 ∨ j = o + 2 ∨ j = o + 3 := by omega
      have h0 : o < l.length := by omega
      have h1 : o + 1 < l.length := by omega
      have h2 : o + 2 < l.length := by omega
      have h3 : o + 3 < l.length := by omega
      rcases this with h' | h' | h' | h' <;> subst h' <;> simp [h0, h1, h2, h3] <;> omega
    · simp [hj4, hj]; omega

/-! ## RGBA encoding of pixel lists -/

def rgbaL (ps : List Pixel) : List UInt8 := ps.flatMap fun p => [p.r, p.g, p.b, p.a]

@[simp] theorem rgbaL_nil : rgbaL [] = [] := rfl
@[simp] theorem rgbaL_cons (p : Pixel) (ps : List Pixel) :
    rgbaL (p :: ps) = p.r :: p.g :: p.b :: p.a :: rgbaL ps := rfl
theorem rgbaL_append (ps qs : List Pixel) : rgbaL (ps ++ qs) = rgbaL ps ++ rgbaL qs := by
  simp [rgbaL]
@[simp] theorem length_rgbaL (ps : List Pixel) : (rgbaL ps).length = 4 * ps.length := by
  induction ps <;> simp [*]; omega

theorem rgbaL_replicate_succ (n : Nat) (p : Pixel) :
    rgbaL (List.replicate (n + 1) p) = [p.r, p.g, p.b, p.a] ++ rgbaL (List.replicate n p) := rfl

/-! ## The implementation's building blocks -/

theorem Nat.land_63 (x : Nat) : x &&& 63 = x % 64 := Nat.and_two_pow_sub_one_eq_mod x 6
theorem Nat.land_3 (x : Nat) : x &&& 3 = x % 4 := Nat.and_two_pow_sub_one_eq_mod x 2

/-- Facts about `UInt8` comparisons, shifts and masks: go to `Nat` and use `omega`. -/
macro "u8_arith" : tactic => `(tactic| (
  simp only [UInt8.lt_iff_toNat_lt, UInt8.le_iff_toNat_le, ← UInt8.toNat_inj, UInt8.toNat_shiftRight,
    Nat.shiftRight_eq_div_pow, UInt8.toNat_ofNat, UInt8.toNat_and, Nat.land_63, Nat.land_3,
    UInt8.toNat_add, UInt8.toNat_mul, ne_eq, Nat.reducePow, Nat.reduceMod] at * <;> omega))

theorem data_put4 (out : ByteArray) (o : USize) (r g b a : UInt8) (h hs) :
    (put4 out o r g b a h hs).data.toList =
      (((out.data.toList.set o.toNat r).set (o.toNat + 1) g).set (o.toNat + 2) b).set (o.toNat + 3) a := by
  have h1 : (o + 1).toNat = o.toNat + 1 := by usize_arith
  have h2 : (o + 2).toNat = o.toNat + 2 := by usize_arith
  have h3 : (o + 3).toNat = o.toNat + 3 := by usize_arith
  simp [put4, data_uset, h1, h2, h3]

theorem take_put4 (out : ByteArray) (o : USize) (r g b a : UInt8) (h hs) :
    (put4 out o r g b a h hs).data.toList.take (o.toNat + 4) = out.data.toList.take o.toNat ++ [r, g, b, a] := by
  rw [data_put4]; exact take_set4 _ _ _ _ _ _ (by simpa using h)

/-- The pixel a packed `UInt32` stands for. -/
def unpack (p : UInt32) : Pixel := ⟨p.toUInt8, (p >>> 8).toUInt8, (p >>> 16).toUInt8, (p >>> 24).toUInt8⟩

theorem unpack_pk (r g b a : UInt8) : unpack (pk r g b a) = ⟨r, g, b, a⟩ := by
  have hr := UInt8.toNat_lt r; have hg := UInt8.toNat_lt g
  have hb := UInt8.toNat_lt b; have ha := UInt8.toNat_lt a
  have hp : (pk r g b a).toNat = r.toNat + g.toNat * 256 + b.toNat * 65536 + a.toNat * 16777216 := by
    simp only [pk, UInt32.toNat_add, UInt32.toNat_mul, UInt8.toNat_toUInt32, UInt32.reduceToNat]
    omega
  simp only [unpack, Pixel.mk.injEq, ← UInt8.toNat_inj, UInt32.toNat_toUInt8, UInt32.toNat_shiftRight,
    Nat.shiftRight_eq_div_pow, hp, UInt32.reduceToNat, Nat.reduceMod, Nat.reducePow]
  omega

theorem take_fill (out : ByteArray) (hs) (o n : USize) (p : UInt32) (h) :
    (fill out hs o n p h).data.toList.take (o.toNat + 4 * n.toNat) =
      out.data.toList.take o.toNat ++ rgbaL (List.replicate n.toNat (unpack p)) := by
  fun_induction fill out hs o n p h with
  | case1 => simp
  | case2 out hs o n h hn ih =>
    have hn' := hn; have h' := h; have hs' := hs
    have e1 : (o + 4).toNat + 4 * (n - 1).toNat = o.toNat + 4 * n.toNat := by clear ih; usize_arith
    have e2 : n.toNat = (n - 1).toNat + 1 := by clear ih; usize_arith
    have e3 : (o + 4).toNat = o.toNat + 4 := by clear ih; usize_arith
    rw [← e1, ih, e3, take_put4, e2, rgbaL_replicate_succ, List.append_assoc]
    rfl

theorem hashIdx_eq (r g b a : UInt8) : (hashIdx r g b a).toNat = (Pixel.hash ⟨r, g, b, a⟩).val := by
  have : ((r * 3 + g * 5 + b * 7 + a * 11) &&& 63).toNat =
      (r.toNat * 3 + g.toNat * 5 + b.toNat * 7 + a.toNat * 11) % 64 := by u8_arith
  simp only [hashIdx, Pixel.hash]
  usize_arith

/-- The index of packed pixels represents the spec's `Vector Pixel 64`. -/
def IdxRel (idx : Array UInt32) (I : Vector Pixel 64) : Prop := idx.toList.map unpack = I.toList

theorem IdxRel.set {idx : Array UInt32} {I : Vector Pixel 64} (hI : IdxRel idx I) (v : UInt32)
    (r g b a : UInt8) (hv : unpack v = ⟨r, g, b, a⟩) (h) :
    IdxRel (idx.uset (hashIdx r g b a) v h) (I.set (Pixel.hash ⟨r, g, b, a⟩) ⟨r, g, b, a⟩) := by
  unfold IdxRel at *
  rw [Array.uset_eq_set, Array.toList_set, List.map_set, hv, hashIdx_eq, Vector.toList_set, hI]

theorem IdxRel.get {idx : Array UInt32} {I : Vector Pixel 64} (hI : IdxRel idx I) (t : UInt8) (ht : t < 64)
    (h) : unpack (idx.uget t.toUSize h) = I[t.toNat % 64] := by
  have ht' : t.toNat < 64 := by u8_arith
  have hm : t.toNat % 64 = t.toNat := Nat.mod_eq_of_lt ht'
  unfold IdxRel at hI
  have h2 := congrArg (·[t.toNat]?) hI
  simp only [List.getElem?_map, Array.getElem?_toList, Vector.getElem?_toList] at h2
  simp only [hm, Array.uget, UInt8.toNat_toUSize]
  rw [Array.getElem?_eq_getElem (by simpa using h), Vector.getElem?_eq_getElem ht'] at h2
  simpa using h2

/-! ## The spec, one chunk at a time -/

section chunks
variable (I : Vector Pixel 64) (P : Pixel) (tag : UInt8) (rest : List UInt8)

theorem chunk_index (h : tag < 0x40) : chunk I P (tag :: rest) = some (I[tag.toNat % 64], 0, rest) := by
  have : tag ≠ 0xFE ∧ tag ≠ 0xFF ∧ tag >>> 6 = 0 := by u8_arith
  simp [chunk, this]

theorem chunk_diff (h1 : ¬tag < 0x40) (h2 : tag < 0x80) :
    chunk I P (tag :: rest) = some (⟨P.r + (tag >>> 4 &&& 3) - 2,
      P.g + (tag >>> 2 &&& 3) - 2, P.b + (tag &&& 3) - 2, P.a⟩, 0, rest) := by
  have : tag ≠ 0xFE ∧ tag ≠ 0xFF ∧ tag >>> 6 ≠ 0 ∧ tag >>> 6 = 1 := by u8_arith
  simp [chunk, this]

theorem chunk_luma (h1 : ¬tag < 0x80) (h2 : tag < 0xC0) (next : UInt8) :
    chunk I P (tag :: next :: rest) = some (⟨P.r + ((tag &&& (63 : UInt8)) - 32) + (next >>> (4 : UInt8)) - 8,
      P.g + ((tag &&& (63 : UInt8)) - 32), P.b + ((tag &&& (63 : UInt8)) - 32) + (next &&& (15 : UInt8)) - 8, P.a⟩, 0, rest) := by
  have : tag ≠ 0xFE ∧ tag ≠ 0xFF ∧ tag >>> 6 ≠ 0 ∧ tag >>> 6 ≠ 1 ∧ tag >>> 6 = 2 := by u8_arith
  simp [chunk, this]

theorem chunk_luma_none (h1 : ¬tag < 0x80) (h2 : tag < 0xC0) : chunk I P [tag] = none := by
  have : tag ≠ 0xFE ∧ tag ≠ 0xFF ∧ tag >>> 6 ≠ 0 ∧ tag >>> 6 ≠ 1 ∧ tag >>> 6 = 2 := by u8_arith
  simp [chunk, this]

theorem chunk_run (h1 : ¬tag < 0xC0) (h2 : ¬tag = 0xFE) (h3 : ¬tag = 0xFF) :
    chunk I P (tag :: rest) = some (P, (tag &&& 63).toNat, rest) := by
  have : tag >>> 6 ≠ 0 ∧ tag >>> 6 ≠ 1 ∧ tag >>> 6 ≠ 2 := by u8_arith
  simp [chunk, this, h2, h3]

theorem chunk_rgb (h : tag = 0xFE) (r g b : UInt8) :
    chunk I P (tag :: r :: g :: b :: rest) = some (⟨r, g, b, P.a⟩, 0, rest) := by
  subst h; simp [chunk]

theorem chunk_rgb_none (ht : tag = 0xFE) (h : rest.length < 3) : chunk I P (tag :: rest) = none := by
  subst ht
  match rest, h with
  | [], _ | [_], _ | [_, _], _ => simp [chunk]

theorem chunk_rgba (h : tag = 0xFF) (r g b a : UInt8) :
    chunk I P (tag :: r :: g :: b :: a :: rest) = some (⟨r, g, b, a⟩, 0, rest) := by
  subst h; simp [chunk]

theorem chunk_rgba_none (ht : tag = 0xFF) (h : rest.length < 4) :
    chunk I P (tag :: rest) = none := by
  subst ht
  match rest, h with
  | [], _ | [_], _ | [_, _], _ | [_, _, _], _ => simp [chunk]

end chunks

theorem pixels_single (n : Nat) (I : Vector Pixel 64) (P : Pixel) (L : List UInt8) (px : Pixel)
    (rest : List UInt8) (h : chunk I P L = some (px, 0, rest)) :
    pixels (n + 1) I P L = (pixels n (I.set px.hash px) px rest).map (px :: ·) := by
  simp [pixels, h]
  generalize pixels _ _ _ _ = x; cases x <;> rfl

theorem pixels_run (n : Nat) (I : Vector Pixel 64) (P : Pixel) (L : List UInt8) (px : Pixel) (c : Nat)
    (rest : List UInt8) (h : chunk I P L = some (px, c, rest)) :
    pixels (n + 1) I P L =
      (pixels (n - min c n) (I.set px.hash px) px rest).map (List.replicate (min c n + 1) px ++ ·) := by
  simp [pixels, h]
  generalize pixels _ _ _ _ = x; cases x <;> rfl

theorem pixels_none (n : Nat) (I : Vector Pixel 64) (P : Pixel) (L : List UInt8)
    (h : chunk I P L = none) : pixels (n + 1) I P L = none := by
  simp [pixels, h]

/-! ## The loop -/

/-- The chunk bytes from position `pos` on. -/
def rest (b : ByteArray) (e pos : USize) : List UInt8 := (b.data.toList.take e.toNat).drop pos.toNat

theorem rest_succ (b : ByteArray) (e : USize) (he : e.toNat + 8 ≤ b.size) (p q : USize)
    (hq : q.toNat = p.toNat + 1) (hp : p.toNat < e.toNat) (h) :
    rest b e p = b.uget p h :: rest b e q := by
  simp only [rest, hq, uget_eq]
  rw [List.drop_eq_getElem_cons (by simp; omega), List.getElem_take]

theorem rest_length (b : ByteArray) (e : USize) (he : e.toNat + 8 ≤ b.size) (p : USize) :
    (rest b e p).length = e.toNat - p.toNat := by
  simp [rest]; omega

theorem rest_eq_nil (b : ByteArray) (e : USize) (he : e.toNat + 8 ≤ b.size) (p : USize)
    (h : e.toNat ≤ p.toNat) : rest b e p = [] := by
  rw [← List.length_eq_zero_iff, rest_length b e he]; omega

theorem toNat_add_lit (p : USize) (n : Nat) (h : p.toNat + n < USize.size) :
    (p + OfNat.ofNat n).toNat = p.toNat + n := by
  have : n < USize.size := by omega
  usize_arith

theorem toNat_add_4mul (o n : USize) (h : o.toNat + 4 * n.toNat < USize.size) :
    (o + 4 * n).toNat = o.toNat + 4 * n.toNat := by usize_arith

theorem toNat_4mul (n : USize) (h : 4 * n.toNat < USize.size) : (4 * n).toNat = 4 * n.toNat := by
  usize_arith

theorem toNat_quarter (o oe : USize) (h : o.toNat ≤ oe.toNat) : ((oe - o) / 4).toNat = (oe.toNat - o.toNat) / 4 := by
  rw [USize.toNat_div, USize.toNat_sub_of_le _ _ (USize.le_iff_toNat_le.mpr h)]
  have : (4 : USize).toNat = 4 := by
    rcases System.Platform.numBits_eq with h | h <;> simp [h]
  rw [this]

theorem take_rgbaL_replicate (P : Pixel) (n m : Nat) (h : n ≤ m) :
    (rgbaL (List.replicate m P)).take (4 * n) = rgbaL (List.replicate n P) := by
  rw [show m = n + (m - n) by omega, ← List.replicate_append_replicate, rgbaL_append, List.take_append]
  simp [List.take_of_length_le]

theorem take_copy_hit (pat out : ByteArray) (o n : Nat) (hpat : pat.size = 256) (hn : n ≤ 64)
    (h : o + 4 * n ≤ out.size) :
    (pat.copySlice 0 out o (4 * n)).data.toList.take (o + 4 * n) =
      out.data.toList.take o ++ pat.data.toList.take (4 * n) := by
  have h1 : min o out.size = o := by omega
  have h2 : min (4 * n) pat.size = 4 * n := by omega
  rw [ByteArray.copySlice_eq_append]
  simp [ByteArray.data_append, ByteArray.data_extract, List.take_append, h1, h2, List.take_take]

theorem take_copy_pat (src pat : ByteArray) (o len : Nat) (h : o + len ≤ src.size) :
    (src.copySlice o pat 0 len).data.toList.take len = (src.data.toList.drop o).take len := by
  have h1 : min len (src.size - o) = len := by omega
  rw [ByteArray.copySlice_eq_append]
  simp [ByteArray.data_append, ByteArray.data_extract, List.take_append, h1, List.take_take]

theorem single_step (X : Option ByteArray) (k : Nat) (hk : 0 < k) (I : Vector Pixel 64) (P px : Pixel)
    (L L' : List UInt8) (hch : chunk I P L = some (px, 0, L')) (out out' : ByteArray) (o o' : Nat)
    (hout : out'.data.toList.take o' = out.data.toList.take o ++ [px.r, px.g, px.b, px.a])
    (ih : X = (pixels (k - 1) (I.set px.hash px) px L').map
      fun ps => ⟨(out'.data.toList.take o' ++ rgbaL ps).toArray⟩) :
    X = (pixels k I P L).map fun ps => ⟨(out.data.toList.take o ++ rgbaL ps).toArray⟩ := by
  obtain ⟨m, rfl⟩ : ∃ m, k = m + 1 := ⟨k - 1, by omega⟩
  rw [ih, pixels_single _ _ _ _ _ _ hch, Option.map_map]
  congr 1; funext ps
  simp [hout]

theorem none_step (k : Nat) (hk : 0 < k) (I : Vector Pixel 64) (P : Pixel) (L : List UInt8)
    (hch : chunk I P L = none) (f : List Pixel → ByteArray) :
    none = (pixels k I P L).map f := by
  obtain ⟨m, rfl⟩ : ∃ m, k = m + 1 := ⟨k - 1, by omega⟩
  rw [pixels_none _ _ _ _ hch]; rfl

theorem runLen_toNat (tag : UInt8) (k : USize) (hk : ¬k = 0) :
    (runLen tag k).toNat = min (tag &&& 63).toNat (k.toNat - 1) + 1 := by
  have : (tag &&& 63).toNat ≤ 63 := by rw [UInt8.toNat_and]; exact Nat.and_le_right
  have := USize.toNat_lt_size k
  simp only [runLen]; split <;> usize_arith

theorem run_step (X : Option ByteArray) (k n : Nat) (hk : 0 < k) (I : Vector Pixel 64) (P : Pixel)
    (L L' : List UInt8) (c : Nat) (hch : chunk I P L = some (P, c, L'))
    (hn : n = min c (k - 1) + 1) (out out' : ByteArray) (o o' : Nat)
    (hout : out'.data.toList.take o' = out.data.toList.take o ++ rgbaL (List.replicate n P))
    (ih : X = (pixels (k - n) (I.set P.hash P) P L').map
      fun ps => ⟨(out'.data.toList.take o' ++ rgbaL ps).toArray⟩) :
    X = (pixels k I P L).map fun ps => ⟨(out.data.toList.take o ++ rgbaL ps).toArray⟩ := by
  obtain ⟨m, rfl⟩ : ∃ m, k = m + 1 := ⟨k - 1, by omega⟩
  have hkn : m + 1 - n = m - min c m := by omega
  have hn' : n = min c m + 1 := by simpa using hn
  rw [ih, pixels_run _ _ _ _ _ _ _ hch, Option.map_map, hkn, ← hn']
  congr 1; funext ps
  simp [hout, rgbaL_append]

theorem loop_eq (pr pg pb pa : UInt8) (pos o : USize) (idx : Array UInt32) (out : ByteArray)
    (b : ByteArray) (e oe : USize) (pat : ByteArray) (pp : UInt32) (pl : USize) (he hbs hidx hpat hs hpos hoe ho)
    (I : Vector Pixel 64) (hI : IdxRel idx I)
    (hPat : pat.data.toList.take (4 * pl.toNat) = rgbaL (List.replicate pl.toNat (unpack pp))) :
    loop pr pg pb pa pos o idx out b e oe pat pp pl he hbs hidx hpat hs hpos hoe ho =
      (pixels ((oe.toNat - o.toNat) / 4) I ⟨pr, pg, pb, pa⟩ (rest b e pos)).map
        fun ps => ⟨(out.data.toList.take o.toNat ++ rgbaL ps).toArray⟩ := by
  have hE := he
  have hB := hbs
  fun_induction loop pr pg pb pa pos o idx out b e oe pat pp pl he hbs hidx hpat hs hpos hoe ho generalizing I with
  | case1 pr pg pb pa pos o idx out pat pp pl hidx hpat hs hpos hoe ho hk hp tag hRGB h3 r g bl ih =>
    -- QOI_OP_RGB
    have hP := USize.le_iff_toNat_le.mp hpos
    have hpe := USize.lt_iff_toNat_lt.mp hp
    have hko := USize.lt_iff_toNat_lt.mp hk
    have hq1 : (pos + 1).toNat = pos.toNat + 1 := toNat_add_lit pos 1 (by omega)
    have hq2 : (pos + 2).toNat = pos.toNat + 2 := toNat_add_lit pos 2 (by omega)
    have hq3 : (pos + 3).toNat = pos.toNat + 3 := toNat_add_lit pos 3 (by omega)
    have hq4 : (pos + 4).toNat = pos.toNat + 4 := toNat_add_lit pos 4 (by omega)
    have h3' := USize.lt_iff_toNat_lt.mp h3
    have ho4 : (o + 4).toNat = o.toNat + 4 := toNat_add_lit o 4 (by omega)
    have ih' := ih _ (hI.set (pk r g bl pa) r g bl pa (unpack_pk ..) _) hPat
    rw [ho4, show (oe.toNat - (o.toNat + 4)) / 4 = (oe.toNat - o.toNat) / 4 - 1 by omega] at ih'
    refine single_step _ _ (by omega) I ⟨pr, pg, pb, pa⟩ ⟨r, g, bl, pa⟩ (rest b e pos) (rest b e (pos + 4))
      ?_ out _ o.toNat (o.toNat + 4) (take_put4 ..) ih'
    rw [rest_succ b e hE pos (pos + 1) hq1 hpe (by omega),
      rest_succ b e hE (pos + 1) (pos + 2) (by omega) (by omega) (by omega),
      rest_succ b e hE (pos + 2) (pos + 3) (by omega) (by omega) (by omega),
      rest_succ b e hE (pos + 3) (pos + 4) (by omega) (by omega) (by omega)]
    exact chunk_rgb I _ tag _ hRGB r g bl
  | case2 pr pg pb pa pos o idx out pat pp pl hidx hpat hs hpos hoe ho hk hp tag hRGB h3 =>
    -- QOI_OP_RGB, cut off
    have hP := USize.le_iff_toNat_le.mp hpos
    have hpe := USize.lt_iff_toNat_lt.mp hp
    have hko := USize.lt_iff_toNat_lt.mp hk
    have hq1 : (pos + 1).toNat = pos.toNat + 1 := toNat_add_lit pos 1 (by omega)
    have hq3 : (pos + 3).toNat = pos.toNat + 3 := toNat_add_lit pos 3 (by omega)
    have h3' := mt USize.lt_iff_toNat_lt.mpr h3
    have hlen : (rest b e (pos + 1)).length < 3 := by rw [rest_length b e hE]; omega
    refine none_step _ (by omega) I _ _ ?_ _
    rw [rest_succ b e hE pos (pos + 1) hq1 hpe (by omega)]
    exact chunk_rgb_none I _ tag _ hRGB hlen
  | case3 pr pg pb pa pos o idx out pat pp pl hidx hpat hs hpos hoe ho hk hp tag hRGB hFF h4 r g bl a ih =>
    -- QOI_OP_RGBA
    have hP := USize.le_iff_toNat_le.mp hpos
    have hpe := USize.lt_iff_toNat_lt.mp hp
    have hko := USize.lt_iff_toNat_lt.mp hk
    have hq1 : (pos + 1).toNat = pos.toNat + 1 := toNat_add_lit pos 1 (by omega)
    have hq2 : (pos + 2).toNat = pos.toNat + 2 := toNat_add_lit pos 2 (by omega)
    have hq3 : (pos + 3).toNat = pos.toNat + 3 := toNat_add_lit pos 3 (by omega)
    have hq4 : (pos + 4).toNat = pos.toNat + 4 := toNat_add_lit pos 4 (by omega)
    have hq5 : (pos + 5).toNat = pos.toNat + 5 := toNat_add_lit pos 5 (by omega)
    have h4' := USize.lt_iff_toNat_lt.mp h4
    have ho4 : (o + 4).toNat = o.toNat + 4 := toNat_add_lit o 4 (by omega)
    have ih' := ih _ (hI.set (pk r g bl a) r g bl a (unpack_pk ..) _) hPat
    rw [ho4, show (oe.toNat - (o.toNat + 4)) / 4 = (oe.toNat - o.toNat) / 4 - 1 by omega] at ih'
    refine single_step _ _ (by omega) I ⟨pr, pg, pb, pa⟩ ⟨r, g, bl, a⟩ (rest b e pos) (rest b e (pos + 5))
      ?_ out _ o.toNat (o.toNat + 4) (take_put4 ..) ih'
    rw [rest_succ b e hE pos (pos + 1) hq1 hpe (by omega),
      rest_succ b e hE (pos + 1) (pos + 2) (by omega) (by omega) (by omega),
      rest_succ b e hE (pos + 2) (pos + 3) (by omega) (by omega) (by omega),
      rest_succ b e hE (pos + 3) (pos + 4) (by omega) (by omega) (by omega),
      rest_succ b e hE (pos + 4) (pos + 5) (by omega) (by omega) (by omega)]
    exact chunk_rgba I _ tag _ hFF r g bl a
  | case4 pr pg pb pa pos o idx out pat pp pl hidx hpat hs hpos hoe ho hk hp tag hRGB hFF h4 =>
    -- QOI_OP_RGBA, cut off
    have hP := USize.le_iff_toNat_le.mp hpos
    have hpe := USize.lt_iff_toNat_lt.mp hp
    have hko := USize.lt_iff_toNat_lt.mp hk
    have hq1 : (pos + 1).toNat = pos.toNat + 1 := toNat_add_lit pos 1 (by omega)
    have hq4 : (pos + 4).toNat = pos.toNat + 4 := toNat_add_lit pos 4 (by omega)
    have h4' := mt USize.lt_iff_toNat_lt.mpr h4
    have hlen : (rest b e (pos + 1)).length < 4 := by rw [rest_length b e hE]; omega
    refine none_step _ (by omega) I _ _ ?_ _
    rw [rest_succ b e hE pos (pos + 1) hq1 hpe (by omega)]
    exact chunk_rgba_none I _ tag _ hFF hlen
  | case5 pr pg pb pa pos o idx out pat pp pl hidx hpat hs hpos hoe ho hk hp tag hRGB hFF h40 ht p r g bl a ih =>
    -- QOI_OP_INDEX
    have hP := USize.le_iff_toNat_le.mp hpos
    have hpe := USize.lt_iff_toNat_lt.mp hp
    have hko := USize.lt_iff_toNat_lt.mp hk
    have hq : (pos + 1).toNat = pos.toNat + 1 := toNat_add_lit pos 1 (by omega)
    have ho4 : (o + 4).toNat = o.toNat + 4 := toNat_add_lit o 4 (by omega)
    have hpx : (⟨r, g, bl, a⟩ : Pixel) = I[tag.toNat % 64] := hI.get tag h40 ht
    have ih' := ih _ (hI.set p r g bl a rfl _) hPat
    rw [ho4, show (oe.toNat - (o.toNat + 4)) / 4 = (oe.toNat - o.toNat) / 4 - 1 by omega] at ih'
    refine single_step _ _ (by omega) I ⟨pr, pg, pb, pa⟩ ⟨r, g, bl, a⟩ (rest b e pos) (rest b e (pos + 1))
      ?_ out _ o.toNat (o.toNat + 4) (take_put4 ..) ih'
    rw [rest_succ b e hE pos (pos + 1) hq hpe (by omega), hpx]
    exact chunk_index I _ tag _ h40
  | case6 pr pg pb pa pos o idx out pat pp pl hidx hpat hs hpos hoe ho hk hp tag hRGB hFF h40 h80 r g bl ih =>
    -- QOI_OP_DIFF
    have hP := USize.le_iff_toNat_le.mp hpos
    have hpe := USize.lt_iff_toNat_lt.mp hp
    have hko := USize.lt_iff_toNat_lt.mp hk
    have hq : (pos + 1).toNat = pos.toNat + 1 := toNat_add_lit pos 1 (by omega)
    have ho4 : (o + 4).toNat = o.toNat + 4 := toNat_add_lit o 4 (by omega)
    have ih' := ih _ (hI.set (pk r g bl pa) r g bl pa (unpack_pk ..) _) hPat
    rw [ho4, show (oe.toNat - (o.toNat + 4)) / 4 = (oe.toNat - o.toNat) / 4 - 1 by omega] at ih'
    refine single_step _ _ (by omega) I ⟨pr, pg, pb, pa⟩ ⟨r, g, bl, pa⟩ (rest b e pos) (rest b e (pos + 1))
      ?_ out _ o.toNat (o.toNat + 4) (take_put4 ..) ih'
    rw [rest_succ b e hE pos (pos + 1) hq hpe (by omega)]
    exact chunk_diff I _ tag _ h40 h80
  | case7 pr pg pb pa pos o idx out pat pp pl hidx hpat hs hpos hoe ho hk hp tag hRGB hFF h40 h80 hC0 h1 next dg r g bl ih =>
    -- QOI_OP_LUMA
    have hP := USize.le_iff_toNat_le.mp hpos
    have hpe := USize.lt_iff_toNat_lt.mp hp
    have hko := USize.lt_iff_toNat_lt.mp hk
    have hq1 : (pos + 1).toNat = pos.toNat + 1 := toNat_add_lit pos 1 (by omega)
    have hq2 : (pos + 2).toNat = pos.toNat + 2 := toNat_add_lit pos 2 (by omega)
    have h1' := USize.lt_iff_toNat_lt.mp h1
    have ho4 : (o + 4).toNat = o.toNat + 4 := toNat_add_lit o 4 (by omega)
    have ih' := ih _ (hI.set (pk r g bl pa) r g bl pa (unpack_pk ..) _) hPat
    rw [ho4, show (oe.toNat - (o.toNat + 4)) / 4 = (oe.toNat - o.toNat) / 4 - 1 by omega] at ih'
    refine single_step _ _ (by omega) I ⟨pr, pg, pb, pa⟩ ⟨r, g, bl, pa⟩ (rest b e pos) (rest b e (pos + 2))
      ?_ out _ o.toNat (o.toNat + 4) (take_put4 ..) ih'
    rw [rest_succ b e hE pos (pos + 1) hq1 hpe (by omega),
      rest_succ b e hE (pos + 1) (pos + 2) (by omega) (by omega) (by omega)]
    exact chunk_luma I _ tag _ h80 hC0 next
  | case8 pr pg pb pa pos o idx out pat pp pl hidx hpat hs hpos hoe ho hk hp tag hRGB hFF h40 h80 hC0 h1 =>
    -- QOI_OP_LUMA, cut off
    have hP := USize.le_iff_toNat_le.mp hpos
    have hpe := USize.lt_iff_toNat_lt.mp hp
    have hko := USize.lt_iff_toNat_lt.mp hk
    have hq1 : (pos + 1).toNat = pos.toNat + 1 := toNat_add_lit pos 1 (by omega)
    have h1' := mt USize.lt_iff_toNat_lt.mpr h1
    refine none_step _ (by omega) I _ _ ?_ _
    rw [rest_succ b e hE pos (pos + 1) hq1 hpe (by omega), rest_eq_nil b e hE _ (by omega)]
    exact chunk_luma_none I _ tag h80 hC0
  | case9 pr pg pb pa pos o idx out pat pp pl hidx hpat hs hpos hoe ho hk hp tag hRGB hFF h40 h80 hC0 hk' n hn1
      px hshort ih =>
    -- QOI_OP_RUN, short: written pixel by pixel
    have hP := USize.le_iff_toNat_le.mp hpos
    have hpe := USize.lt_iff_toNat_lt.mp hp
    have hko := USize.lt_iff_toNat_lt.mp hk
    have hq : (pos + 1).toNat = pos.toNat + 1 := toNat_add_lit pos 1 (by omega)
    have hK := toNat_quarter o oe (by omega)
    have hn := runLen_toNat tag ((oe - o) / 4) hk'
    rw [hK] at hn hn1
    have hon := toNat_add_4mul o n (by omega)
    have ih' := ih _ (hI.set px pr pg pb pa (unpack_pk ..) _) hPat
    rw [hon, show (oe.toNat - (o.toNat + 4 * n.toNat)) / 4 = (oe.toNat - o.toNat) / 4 - n.toNat by omega] at ih'
    refine run_step _ _ _ (by omega) I ⟨pr, pg, pb, pa⟩ (rest b e pos) (rest b e (pos + 1))
      (tag &&& 63).toNat ?_ hn out _ o.toNat _ ?_ ih'
    · rw [rest_succ b e hE pos (pos + 1) hq hpe (by omega)]
      exact chunk_run I _ tag _ hC0 hRGB hFF
    · rw [take_fill, unpack_pk]
  | case10 pr pg pb pa pos o idx out pat pp pl hidx hpat hs hpos hoe ho hk hp tag hRGB hFF h40 h80 hC0 hk' n
      hn1 px hshort hn64 hhit ih =>
    -- QOI_OP_RUN, long, and the cached pattern has it: one `copySlice`
    have hP := USize.le_iff_toNat_le.mp hpos
    have hpe := USize.lt_iff_toNat_lt.mp hp
    have hko := USize.lt_iff_toNat_lt.mp hk
    have hq : (pos + 1).toNat = pos.toNat + 1 := toNat_add_lit pos 1 (by omega)
    have hK := toNat_quarter o oe (by omega)
    have hn := runLen_toNat tag ((oe - o) / 4) hk'
    rw [hK] at hn hn1
    have hon := toNat_add_4mul o n (by omega)
    have h4n := toNat_4mul n (by omega)
    have hnl := USize.le_iff_toNat_le.mp hhit.2
    have ih' := ih _ (hI.set px pr pg pb pa (unpack_pk ..) _) hPat
    rw [hon, show (oe.toNat - (o.toNat + 4 * n.toNat)) / 4 = (oe.toNat - o.toNat) / 4 - n.toNat by omega] at ih'
    refine run_step _ _ _ (by omega) I ⟨pr, pg, pb, pa⟩ (rest b e pos) (rest b e (pos + 1))
      (tag &&& 63).toNat ?_ hn out _ o.toNat _ ?_ ih'
    · rw [rest_succ b e hE pos (pos + 1) hq hpe (by omega)]
      exact chunk_run I _ tag _ hC0 hRGB hFF
    · rw [h4n, take_copy_hit pat out _ _ hpat hn64 (by omega)]
      rw [show pat.data.toList.take (4 * n.toNat) = (pat.data.toList.take (4 * pl.toNat)).take (4 * n.toNat) by
        rw [List.take_take]; congr 1; omega]
      rw [hPat, take_rgbaL_replicate _ _ _ hnl, hhit.1, unpack_pk]
  | case11 pr pg pb pa pos o idx out pat pp pl hidx hpat hs hpos hoe ho hk hp tag hRGB hFF h40 h80 hC0 hk' n
      hn1 px hshort hn64 hmiss out' ih =>
    -- QOI_OP_RUN, long, not cached: written pixel by pixel, then copied into the pattern
    have hP := USize.le_iff_toNat_le.mp hpos
    have hpe := USize.lt_iff_toNat_lt.mp hp
    have hko := USize.lt_iff_toNat_lt.mp hk
    have hq : (pos + 1).toNat = pos.toNat + 1 := toNat_add_lit pos 1 (by omega)
    have hK := toNat_quarter o oe (by omega)
    have hn := runLen_toNat tag ((oe - o) / 4) hk'
    rw [hK] at hn hn1
    have hon := toNat_add_4mul o n (by omega)
    have h4n := toNat_4mul n (by omega)
    have hout : out'.data.toList.take (o.toNat + 4 * n.toNat) =
        out.data.toList.take o.toNat ++ rgbaL (List.replicate n.toNat (unpack px)) := take_fill ..
    have hPat' : (out'.copySlice o.toNat pat 0 (4 * n).toNat).data.toList.take (4 * n.toNat) =
        rgbaL (List.replicate n.toNat (unpack px)) := by
      have hsz : out'.size = out.size := size_fill ..
      rw [h4n, take_copy_pat _ _ _ _ (by omega), List.take_drop, hout,
        List.drop_left' (by simp; omega)]
    have ih' := ih _ (hI.set px pr pg pb pa (unpack_pk ..) _) hPat'
    rw [hon, show (oe.toNat - (o.toNat + 4 * n.toNat)) / 4 = (oe.toNat - o.toNat) / 4 - n.toNat by omega] at ih'
    refine run_step _ _ _ (by omega) I ⟨pr, pg, pb, pa⟩ (rest b e pos) (rest b e (pos + 1))
      (tag &&& 63).toNat ?_ hn out _ o.toNat _ ?_ ih'
    · rw [rest_succ b e hE pos (pos + 1) hq hpe (by omega)]
      exact chunk_run I _ tag _ hC0 hRGB hFF
    · rw [hout, unpack_pk]
  | case12 pr pg pb pa pos o idx out pat pp pl hidx hpat hs hpos hoe ho hk hp =>
    -- out of chunk bytes
    have hko := USize.lt_iff_toNat_lt.mp hk
    have hp' := mt USize.lt_iff_toNat_lt.mpr hp
    refine none_step _ (by omega) I _ _ ?_ _
    rw [rest_eq_nil b e hE _ (by omega)]
    rfl
  | case13 pr pg pb pa pos o idx out pat pp pl hidx hpat hs hpos hoe ho hk =>
    -- all pixels written: the output is complete
    have hko := mt USize.lt_iff_toNat_lt.mpr hk
    rw [show (oe.toNat - o.toNat) / 4 = 0 by omega]
    simp only [pixels, rgbaL_nil, List.append_nil, Option.map_some]
    rw [List.take_of_length_le (by simp; omega)]

/-! ## The header -/
theorem decode_cons (a0 a1 a2 a3 a4 a5 a6 a7 a8 a9 a10 a11 a12 a13 : UInt8) (body : List UInt8) :
    decode (a0 :: a1 :: a2 :: a3 :: a4 :: a5 :: a6 :: a7 :: a8 :: a9 :: a10 :: a11 :: a12 :: a13 :: body) =
      if a0 = 0x71 ∧ a1 = 0x6F ∧ a2 = 0x69 ∧ a3 = 0x66 then
        if (a12 = 3 ∨ a12 = 4) ∧ a13 ≤ 1 ∧ be32 a4 a5 a6 a7 * be32 a8 a9 a10 a11 ≤ maxPixels ∧ 8 ≤ body.length then
          (pixels (be32 a4 a5 a6 a7 * be32 a8 a9 a10 a11) (Vector.replicate 64 ⟨0, 0, 0, 0⟩) ⟨0, 0, 0, 255⟩
            (body.take (body.length - 8))).map fun px =>
              { width := be32 a4 a5 a6 a7, height := be32 a8 a9 a10 a11, channels := a12, colorspace := a13,
                pixels := px }
        else none
      else none := by
  unfold decode
  split
  · rename_i heq
    simp only [List.cons.injEq] at heq
    obtain ⟨e0, e1, e2, e3, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl⟩ := heq
    rw [if_pos ⟨e0, e1, e2, e3⟩]
    by_cases h1 : a12 = 3 ∨ a12 = 4
    · by_cases h2 : a13 ≤ 1
      · by_cases h3 : be32 a4 a5 a6 a7 * be32 a8 a9 a10 a11 ≤ maxPixels
        · by_cases h4 : 8 ≤ body.length
          · simp only [h1, h2, h3, h4, guard, ite_true, and_self, ge_iff_le]
            generalize pixels _ _ _ _ = x; cases x <;> rfl
          · simp only [h1, h2, h3, h4, guard, ite_true, ite_false, and_self, and_false, ge_iff_le]; rfl
        · simp only [h1, h2, h3, guard, ite_true, ite_false, and_self, and_false, false_and]; rfl
      · simp only [h1, h2, guard, ite_true, ite_false, and_self, and_false, false_and]; rfl
    · simp only [h1, guard, ite_false, false_and]; rfl
  · rename_i hne
    rw [if_neg]
    rintro ⟨rfl, rfl, rfl, rfl⟩
    exact hne _ _ _ _ _ _ _ _ _ _ _ rfl

theorem decode_short (l : List UInt8) (h : l.length < 14) : decode l = none := by
  unfold decode
  split
  · simp at h; omega
  · rfl

theorem cons14 (l : List UInt8) (h : 14 ≤ l.length) :
    l = l[0] :: l[1] :: l[2] :: l[3] :: l[4] :: l[5] :: l[6] :: l[7] :: l[8] :: l[9] :: l[10] :: l[11] ::
      l[12] :: l[13] :: l.drop 14 := by
  refine (List.drop_zero (l := l)).symm.trans ?_
  rw [List.drop_eq_getElem_cons (i := 0) (by omega), List.drop_eq_getElem_cons (i := 1) (by omega),
    List.drop_eq_getElem_cons (i := 2) (by omega), List.drop_eq_getElem_cons (i := 3) (by omega),
    List.drop_eq_getElem_cons (i := 4) (by omega), List.drop_eq_getElem_cons (i := 5) (by omega),
    List.drop_eq_getElem_cons (i := 6) (by omega), List.drop_eq_getElem_cons (i := 7) (by omega),
    List.drop_eq_getElem_cons (i := 8) (by omega), List.drop_eq_getElem_cons (i := 9) (by omega),
    List.drop_eq_getElem_cons (i := 10) (by omega), List.drop_eq_getElem_cons (i := 11) (by omega),
    List.drop_eq_getElem_cons (i := 12) (by omega), List.drop_eq_getElem_cons (i := 13) (by omega)]

theorem cons14' (b : ByteArray) (h : 14 ≤ b.size) :
    b.data.toList = b[0] :: b[1] :: b[2] :: b[3] :: b[4] :: b[5] :: b[6] :: b[7] :: b[8] :: b[9] :: b[10] ::
      b[11] :: b[12] :: b[13] :: b.data.toList.drop 14 := by
  rw [cons14 b.data.toList (by simpa using h)]
  simp [ByteArray.getElem_eq_getElem_data]

theorem idxRel_index0 : IdxRel index0 (Vector.replicate 64 ⟨0, 0, 0, 0⟩) := by
  simp only [IdxRel, index0, Vector.toList_replicate, Array.toList_replicate, List.map_replicate]
  rfl

/-! ## The theorem -/

theorem decodeRGBA_eq_spec' (b : ByteArray) :
    decodeRGBA b = (QOI.Spec.decode b.toList).map fun img => ⟨img.rgba.toArray⟩ := by
  unfold decodeRGBA
  split
  case isFalse => rfl
  case isTrue hbs =>
  rw [toList_eq]
  by_cases h14 : 14 ≤ b.size
  case neg =>
    rw [decode_short _ (by simp; omega), dif_neg (by omega)]; rfl
  rw [cons14' b h14, decode_cons]
  simp only [List.length_drop, length_data_toList]
  split
  case isFalse h22 => simp [show ¬ 8 ≤ b.size - 14 by omega]
  case isTrue h22 =>
  split
  case isFalse hm => rfl
  case isTrue hm =>
  split
  case isFalse hok => rw [if_neg (fun h => hok ⟨h.1, h.2.1, h.2.2.1⟩)]; rfl
  case isTrue hok =>
  rw [if_pos ⟨hok.1, hok.2.1, hok.2.2, by omega⟩]
  rw [loop_eq (I := Vector.replicate 64 ⟨0, 0, 0, 0⟩) (hI := idxRel_index0) (hPat := by simp)]
  have hN : ∀ M, M ≤ 400000000 → ((4 * M).toUSize.toNat - 0) / 4 = M := by
    intro M hM
    rcases System.Platform.numBits_eq with h | h <;> simp [Nat.toUSize_eq, h] <;> omega
  have he : (b.size - 8).toUSize.toNat = b.size - 8 := by
    rcases System.Platform.numBits_eq with h | h <;> simp [Nat.toUSize_eq, h, USize.size_eq_two_pow] at hbs ⊢ <;> omega
  have h14 : (14 : USize).toNat = 14 := by
    rcases System.Platform.numBits_eq with h | h <;> simp
  have hR : rest b (b.size - 8).toUSize 14 = List.take (b.size - 14 - 8) (List.drop 14 b.data.toList) := by
    simp only [rest, he, h14, List.drop_take]
    try rw [show b.size - 8 - 14 = b.size - 14 - 8 by omega]
  rw [USize.toNat_zero, hN _ hok.2.2, hR, Option.map_map]
  simp only [List.take_zero, List.nil_append]
  congr 1

end QOI.Fast

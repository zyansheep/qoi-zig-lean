import QOI.Spec
import QOI.Fast.Tactic

/-!
# QOI decoding: the fast implementation

The decoder proper. Everything here is plain Lean (no `partial`, `unsafe`, `implemented_by` or
`extern`); speed comes from the runtime primitives on `ByteArray`, `Array` and `USize`, and every
bounds proof is an argument that the compiler erases:

* the input is read with `ByteArray.uget` at indices proven in bounds (no runtime check);
* the output is allocated once at its final size (`alloc`) and written with `ByteArray.uset`
  (in place, since it is uniquely referenced; no bounds check);
* the previous pixel lives in four `UInt8` loop arguments (unboxed in the generated C);
* the 64-entry index is an `Array UInt32` of packed pixels (one store per pixel instead of four);
* the main loop is one tail-recursive function, compiled to a C loop; its dispatch order is the
  one `qoi.h` uses (fewer branch mispredictions on photos);
* runs shorter than 16 pixels are written pixel by pixel (`fill`); longer runs are copied with one
  `ByteArray.copySlice` (a `memcpy`) from a 256-byte pattern that holds the pixel of the last long
  run, repeated; the pattern is refreshed from the output just written whenever a long run of another
  pixel (or a longer run) comes along.

The proof that this computes `QOI.Spec.decode` lives in `QOI/Fast/Proof.lean`.
-/

namespace QOI.Fast

theorem size_uset (a : ByteArray) (i : USize) (v : UInt8) (h : i.toNat < a.size) :
    (a.uset i v h).size = a.size := by
  cases a; simp [ByteArray.uset, ByteArray.size]

/-- Store one RGBA pixel at byte offset `o`. -/
@[inline] def put4 (out : ByteArray) (o : USize) (r g b a : UInt8)
    (h : o.toNat + 4 ≤ out.size) (hs : out.size < USize.size) : ByteArray :=
  (((out.uset o r (by omega)).uset (o + 1) g (by rw [size_uset]; usize_arith)).uset (o + 2) b
    (by rw [size_uset, size_uset]; usize_arith)).uset (o + 3) a
    (by rw [size_uset, size_uset, size_uset]; usize_arith)

theorem size_put4 (out : ByteArray) (o : USize) (r g b a : UInt8) (h hs) :
    (put4 out o r g b a h hs).size = out.size := by
  simp [put4, size_uset]

/-- A pixel packed little-endian into a `UInt32`: the form of index entries and run pixels. -/
@[inline] def pk (r g b a : UInt8) : UInt32 :=
  r.toUInt32 + g.toUInt32 * 256 + b.toUInt32 * 65536 + a.toUInt32 * 16777216

/-- Slot of a pixel in the index. -/
@[inline] def hashIdx (r g b a : UInt8) : USize :=
  ((r * 3 + g * 5 + b * 7 + a * 11) &&& 63).toUSize

theorem hashIdx_lt (r g b a : UInt8) : (hashIdx r g b a).toNat < 64 := by
  have : ((r * 3 + g * 5 + b * 7 + a * 11) &&& 63).toNat ≤ 63 := by
    rw [UInt8.toNat_and]; exact Nat.and_le_right
  simp only [hashIdx]; usize_arith

/-- Write a run of `n` copies of a (packed) pixel starting at byte offset `o`. The pixel is passed
packed so that the loop keeps only four values live (they all fit in callee-saved registers). -/
def fill (out : ByteArray) (hs : out.size < USize.size) (o n : USize) (p : UInt32)
    (h : o.toNat + 4 * n.toNat ≤ out.size) : ByteArray :=
  if hn : n = 0 then out
  else
    fill (put4 out o p.toUInt8 (p >>> 8).toUInt8 (p >>> 16).toUInt8 (p >>> 24).toUInt8 (by usize_arith) hs)
      (by rw [size_put4]; exact hs) (o + 4) (n - 1) p (by rw [size_put4]; usize_arith)
termination_by n.toNat
decreasing_by usize_arith

theorem size_fill (out : ByteArray) (hs) (o n : USize) (p : UInt32) (h) :
    (fill out hs o n p h).size = out.size := by
  fun_induction fill out hs o n p h with
  | case1 => rfl
  | case2 => rename_i ih; rw [ih, size_put4]

/-- Length of a run: `(tag &&& 63) + 1`, cut to the `k` pixels still missing. -/
@[inline] def runLen (tag : UInt8) (k : USize) : USize :=
  let c : USize := (tag &&& 63).toUSize + 1
  if c < k then c else k

theorem runLen_spec (tag : UInt8) (k : USize) (hk : ¬k = 0) :
    1 ≤ (runLen tag k).toNat ∧ (runLen tag k).toNat ≤ k.toNat := by
  have : (tag &&& 63).toNat ≤ 63 := by rw [UInt8.toNat_and]; exact Nat.and_le_right
  simp only [runLen]; split <;> usize_arith

theorem run_dec (tag : UInt8) (o oe : USize) (out : ByteArray) (hs : out.size < USize.size)
    (hoe : oe.toNat = out.size) (hk : o < oe) (ho : o.toNat ≤ oe.toNat ∧ (oe.toNat - o.toNat) % 4 = 0) :
    oe.toNat - (o + 4 * runLen tag ((oe - o) / 4)).toNat < oe.toNat - o.toNat := by
  have hk' : ¬(oe - o) / 4 = 0 := by usize_arith
  have := runLen_spec tag ((oe - o) / 4) hk'
  usize_arith

theorem size_copyRun (pat out : ByteArray) (o n : USize) (hpat : pat.size = 256) (hn : n.toNat ≤ 64)
    (h : o.toNat + 4 * n.toNat ≤ out.size) :
    (pat.copySlice 0 out o.toNat (4 * n).toNat).size = out.size := by
  have : (4 * n).toNat = 4 * n.toNat := by usize_arith
  simp only [ByteArray.copySlice_eq_append, ByteArray.size_append, ByteArray.size_extract, ByteArray.size_data,
    this, hpat]
  omega

theorem size_copyPat (src dest : ByteArray) (srcOff len : Nat) (hdest : dest.size = 256) (hlen : len ≤ 256) :
    (src.copySlice srcOff dest 0 len).size = 256 := by
  simp only [ByteArray.copySlice_eq_append, ByteArray.size_append, ByteArray.size_extract, ByteArray.size_data,
    hdest]
  omega

/-- The decoding loop.
* `(pr, pg, pb, pa)`: the previous pixel; `idx`: the index;
* `pos`: input position; chunks end at `e` (where the 8-byte end marker starts);
* `o`: output byte offset; the output ends at `oe`, so `(oe - o) / 4` pixels are still missing;
* `pat`, `pp`, `pl`: the run pattern; its first `4 * pl` bytes are `pl` copies of the pixel `pp`.

The arguments that change on every step come first, so that they are passed in registers. -/
def loop (pr pg pb pa : UInt8) (pos o : USize) (idx : Array UInt32) (out : ByteArray)
    (b : ByteArray) (e oe : USize) (pat : ByteArray) (pp : UInt32) (pl : USize)
    (he : e.toNat + 8 ≤ b.size) (hbs : b.size < USize.size) (hidx : idx.size = 64) (hpat : pat.size = 256)
    (hs : out.size < USize.size) (hpos : pos ≤ e) (hoe : oe.toNat = out.size)
    (ho : o.toNat ≤ oe.toNat ∧ (oe.toNat - o.toNat) % 4 = 0) : Option ByteArray :=
  if hk : o < oe then
  if hp : pos < e then
    let tag := b.uget pos (by usize_arith)
    if hRGB : tag = 0xFE then
      -- QOI_OP_RGB
      if h3 : pos + 3 < e then
        let r := b.uget (pos + 1) (by usize_arith)
        let g := b.uget (pos + 2) (by usize_arith)
        let bl := b.uget (pos + 3) (by usize_arith)
        loop r g bl pa (pos + 4) (o + 4)
          (idx.uset (hashIdx r g bl pa) (pk r g bl pa) (by have := hashIdx_lt r g bl pa; omega))
          (put4 out o r g bl pa (by usize_arith) hs) b e oe pat pp pl he hbs (by simp [hidx]) hpat
          (by rw [size_put4]; exact hs) (by usize_arith) (by rw [size_put4]; exact hoe) (by usize_arith)
      else none
    else if hFF : tag = 0xFF then
      -- QOI_OP_RGBA
      if h4 : pos + 4 < e then
        let r := b.uget (pos + 1) (by usize_arith)
        let g := b.uget (pos + 2) (by usize_arith)
        let bl := b.uget (pos + 3) (by usize_arith)
        let a := b.uget (pos + 4) (by usize_arith)
        loop r g bl a (pos + 5) (o + 4)
          (idx.uset (hashIdx r g bl a) (pk r g bl a) (by have := hashIdx_lt r g bl a; omega))
          (put4 out o r g bl a (by usize_arith) hs) b e oe pat pp pl he hbs (by simp [hidx]) hpat
          (by rw [size_put4]; exact hs) (by usize_arith) (by rw [size_put4]; exact hoe) (by usize_arith)
      else none
    else if h40 : tag < 0x40 then
      -- QOI_OP_INDEX
      have ht : tag.toUSize.toNat < idx.size := by
        have : tag.toNat < 64 := by rw [UInt8.lt_iff_toNat_lt] at *; simpa using h40
        rw [hidx]; usize_arith
      let p := idx.uget tag.toUSize ht
      let r := p.toUInt8
      let g := (p >>> 8).toUInt8
      let bl := (p >>> 16).toUInt8
      let a := (p >>> 24).toUInt8
      loop r g bl a (pos + 1) (o + 4)
        (idx.uset (hashIdx r g bl a) p (by have := hashIdx_lt r g bl a; omega))
        (put4 out o r g bl a (by usize_arith) hs) b e oe pat pp pl he hbs (by simp [hidx]) hpat
        (by rw [size_put4]; exact hs) (by usize_arith) (by rw [size_put4]; exact hoe) (by usize_arith)
    else if h80 : tag < 0x80 then
      -- QOI_OP_DIFF
      let r := pr + (tag >>> 4 &&& 3) - 2
      let g := pg + (tag >>> 2 &&& 3) - 2
      let bl := pb + (tag &&& 3) - 2
      loop r g bl pa (pos + 1) (o + 4)
        (idx.uset (hashIdx r g bl pa) (pk r g bl pa) (by have := hashIdx_lt r g bl pa; omega))
        (put4 out o r g bl pa (by usize_arith) hs) b e oe pat pp pl he hbs (by simp [hidx]) hpat
        (by rw [size_put4]; exact hs) (by usize_arith) (by rw [size_put4]; exact hoe) (by usize_arith)
    else if hC0 : tag < 0xC0 then
      -- QOI_OP_LUMA
      if h1 : pos + 1 < e then
        let next := b.uget (pos + 1) (by usize_arith)
        let dg : UInt8 := (tag &&& 63) - 32
        let r := pr + dg + (next >>> 4) - 8
        let g := pg + dg
        let bl := pb + dg + (next &&& 15) - 8
        loop r g bl pa (pos + 2) (o + 4)
          (idx.uset (hashIdx r g bl pa) (pk r g bl pa) (by have := hashIdx_lt r g bl pa; omega))
          (put4 out o r g bl pa (by usize_arith) hs) b e oe pat pp pl he hbs (by simp [hidx]) hpat
          (by rw [size_put4]; exact hs) (by usize_arith) (by rw [size_put4]; exact hoe) (by usize_arith)
      else none
    else
      -- QOI_OP_RUN
      have hk' : ¬(oe - o) / 4 = 0 := by usize_arith
      let n := runLen tag ((oe - o) / 4)
      have hn1 : 1 ≤ n.toNat ∧ n.toNat ≤ ((oe - o) / 4).toNat := runLen_spec tag ((oe - o) / 4) hk'
      let px := pk pr pg pb pa
      if hshort : n < 16 then
        loop pr pg pb pa (pos + 1) (o + 4 * n)
          (idx.uset (hashIdx pr pg pb pa) px (by have := hashIdx_lt pr pg pb pa; omega))
          (fill out hs o n px (by usize_arith)) b e oe pat pp pl he hbs
          (by simp [hidx]) hpat (by rw [size_fill]; exact hs) (by usize_arith) (by rw [size_fill]; exact hoe)
          (by usize_arith)
      else
        have hn64 : n.toNat ≤ 64 := by
          have : (tag &&& 63).toNat ≤ 63 := by rw [UInt8.toNat_and]; exact Nat.and_le_right
          simp only [n, runLen]; split <;> usize_arith
        if pp = px ∧ n ≤ pl then
          -- the cached pattern holds at least `n` copies of the pixel: one `memcpy`
          loop pr pg pb pa (pos + 1) (o + 4 * n)
            (idx.uset (hashIdx pr pg pb pa) px (by have := hashIdx_lt pr pg pb pa; omega))
            (pat.copySlice 0 out o.toNat (4 * n).toNat) b e oe pat pp pl he hbs
            (by simp [hidx]) hpat (by rw [size_copyRun _ _ _ _ hpat hn64 (by usize_arith)]; exact hs) (by usize_arith)
            (by rw [size_copyRun _ _ _ _ hpat hn64 (by usize_arith)]; exact hoe) (by usize_arith)
        else
          -- write the run, then remember it as the pattern
          let out' := fill out hs o n px (by usize_arith)
          loop pr pg pb pa (pos + 1) (o + 4 * n)
            (idx.uset (hashIdx pr pg pb pa) px (by have := hashIdx_lt pr pg pb pa; omega))
            out' b e oe (out'.copySlice o.toNat pat 0 (4 * n).toNat) px n he hbs
            (by simp [hidx]) (size_copyPat _ _ _ _ hpat (by usize_arith)) (by rw [size_fill]; exact hs)
            (by usize_arith) (by rw [size_fill]; exact hoe) (by usize_arith)
  else none
  else some out
termination_by oe.toNat - o.toNat
decreasing_by all_goals first | usize_arith | exact run_dec _ o oe out hs hoe hk ho

/-- 4 KiB of zeros (a closed term: built once, at program start). -/
def zeros : ByteArray := ⟨Array.replicate 4096 0⟩

theorem size_zeros : zeros.size = 4096 := by
  show (Array.replicate 4096 (0 : UInt8)).size = 4096; exact Array.size_replicate

/-- A byte array of size `n` (contents irrelevant), allocated once with capacity `n` and grown by
`memcpy`-ing from `zeros`. -/
def alloc (n : Nat) (acc : ByteArray := ByteArray.emptyWithCapacity n) : ByteArray :=
  if _h : acc.size < n then
    alloc n (zeros.copySlice 0 acc acc.size (min 4096 (n - acc.size)))
  else acc
termination_by n - acc.size
decreasing_by
  simp only [ByteArray.copySlice_eq_append, ByteArray.size_append, ByteArray.size_extract]
  rw [size_zeros]; omega

theorem size_alloc (n : Nat) (acc : ByteArray) (h : acc.size ≤ n) : (alloc n acc).size = n := by
  fun_induction alloc n acc with
  | case1 acc hlt ih =>
    apply ih
    simp only [ByteArray.copySlice_eq_append, ByteArray.size_append, ByteArray.size_extract]
    rw [size_zeros]; omega
  | case2 acc hge => omega

/-- The index at the start: 64 entries of `(0, 0, 0, 0)`. -/
def index0 : Array UInt32 := Array.replicate 64 0

/-- The initial run pattern: 64 copies of the pixel `0` (packed). -/
def pat0 : ByteArray := fill (alloc 256) (by rw [size_alloc _ _ (Nat.zero_le _)]; usize_arith) 0 64 0
  (by rw [size_alloc _ _ (Nat.zero_le _)]; usize_arith)

theorem size_pat0 : pat0.size = 256 := by rw [pat0, size_fill]; exact size_alloc _ _ (Nat.zero_le _)

/-- Rarely-taken fallback for inputs that do not fit the address space (cannot happen in practice:
the input is in memory). Keeps `decodeRGBA` total and correct without an extra assumption. -/
def slowPath (b : ByteArray) : Option ByteArray :=
  (QOI.Spec.decode b.toList).map fun img => ⟨img.rgba.toArray⟩

def decodeRGBA (b : ByteArray) : Option ByteArray :=
  if hbs : b.size < USize.size then
    if h22 : 22 ≤ b.size then
      if b[0] = 0x71 ∧ b[1] = 0x6F ∧ b[2] = 0x69 ∧ b[3] = 0x66 then
        let w := QOI.Spec.be32 b[4] b[5] b[6] b[7]
        let h := QOI.Spec.be32 b[8] b[9] b[10] b[11]
        let ch := b[12]
        let cs := b[13]
        if hok : (ch = 3 ∨ ch = 4) ∧ cs ≤ 1 ∧ w * h ≤ QOI.Spec.maxPixels then
          let out := alloc (4 * (w * h))
          have hout : out.size = 4 * (w * h) := size_alloc _ _ (Nat.zero_le _)
          have hmax : w * h ≤ 400000000 := by have := hok.2.2; unfold QOI.Spec.maxPixels at this; exact this
          have hn : w * h < USize.size := by
            have := USize.size_eq_two_pow; rcases System.Platform.numBits_eq with h | h <;>
              simp only [h] at * <;> simp [QOI.Spec.maxPixels] at hok <;> omega
          loop 0 0 0 255 14 0 index0 out b (b.size - 8).toUSize (4 * (w * h)).toUSize pat0 0 0 (by usize_arith) hbs
            (by simp [index0]) size_pat0 (by usize_arith) (by usize_arith) (by usize_arith) (by usize_arith)
        else none
      else none
    else none
  else slowPath b

end QOI.Fast

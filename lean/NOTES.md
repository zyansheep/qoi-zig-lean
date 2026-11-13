# Lean decoder: optimisation and proof log

Files: `QOI/Fast/Impl.lean` (the decoder, ~275 lines incl. its bounds-proof lemmas),
`QOI/Fast/Proof.lean` (the correctness proof, ~640 lines), `QOI/Fast/Tactic.lean` (`usize_arith`),
`QOI/Fast.lean` (the theorem + `#print axioms`, printed on every build).

```
theorem QOI.Fast.decodeRGBA_eq_spec (b : ByteArray) :
    decodeRGBA b = (QOI.Spec.decode b.toList).map (fun img => ⟨img.rgba.toArray⟩)
'QOI.Fast.decodeRGBA_eq_spec' depends on axioms: [propext, Classical.choice, Quot.sound]
```

No `sorry`, `native_decide`, `bv_decide` (it relies on `Lean.ofReduceBool`), `implemented_by`, `extern`,
`unsafe` or `partial` anywhere. Only core Lean (no Batteries, no Mathlib). The decode path uses the runtime
primitives `ByteArray.uget/uset/copySlice/size`, `ByteArray.emptyWithCapacity`, `Array.uget/uset` and `USize`/`UInt8`/
`UInt32` arithmetic.

Measurement: Ryzen 7 5700G, `bench/run.py --cpu 6 --seconds 0.5`, Lean 4.34.1, gcc 16.2 (nix wrapper, with its
hardening flags, same as `qoi.h`), `-O3 -march=znver3`. The machine is shared with the Zig agent and other jobs, so
wall-clock numbers moved by up to ±30 % between runs (qoi.h on `testcard`: 410–770 MPx/s). For A/B decisions I
used (a) an interleaved best-of-3 script (`qoi.h` and variants alternated per image) and (b) `perf stat`
user-mode counters (cycles, instructions, branch-misses per pixel), which are much more stable than wall time.

## Final result (v3)

`bench/run.py --cpu 6 --only c-qoi.h,zig-simple,lean-fast --seconds 0.5` (median MPx/s):

| image | qoi.h | zig-simple | lean-fast | lean/qoi.h |
|---|---|---|---|---|
| edgecase | 879 | 1124 | 1231 | 1.40 |
| qoi_logo | 950 | 1613 | 698 | 0.73 |
| testcard | 771 | 807 | 463 | 0.60 |
| testcard_rgba | 752 | 804 | 468 | 0.62 |
| dice | 496 | 563 | 477 | 0.96 |
| kodim10 | 172 | 152 | 135 | 0.79 |
| kodim23 | 155 | 137 | 119 | 0.77 |
| wikipedia_008 | 130 | 124 | 121 | 0.93 |
| synth_flat | 346 | 289 | 463 | 1.34 |
| synth_photo | 106 | 95 | 126 | 1.20 |

**Geomean 0.87–0.90x qoi.h** (two consecutive runs: 0.895x, 0.869x). Fuzz (`bench/fuzz.py --only lean-fast`):
3000 + 3000 cases with the stock script, plus 20 000 cases (seed 777) with a locally patched copy, 0 mismatches.

Clean `lake build` ≈ 45 s wall on the loaded machine; `QOI.Fast.Impl` 16 s (the many `usize_arith` bounds proofs),
`QOI.Fast.Proof` 23 s, C compile < 2 s. (Unloaded: Impl ≈ 7 s, Proof ≈ 9 s.)

## Log of versions

perf numbers are per pixel: cycles / instructions / branch-misses. qoi.h for reference:
testcard 6.0/26.3/0.019, kodim10 26.2/62.6/0.45, wikipedia 29.8/61.9/0.62, synth_photo 33.0/70.5/0.49,
qoi_logo 4.8/19.9/0.03.

### v0: the spec (placeholder) — ~40x slower than qoi.h.

### v1: first proven fast decoder (checkpoint, 0.61–0.63x)
* one tail-recursive `loop` (compiled to a `goto _start` C loop), all positions `USize`;
* input read with `ByteArray.uget` at indices proven in bounds; the generated `loop___redArg` only takes the
  runtime values, every bounds proof is erased;
* output allocated once at full size (`alloc`: `emptyWithCapacity n`, then `copySlice` 4 KiB at a time from a
  4 KiB zero block that is a closed term, i.e. built once at program start), written with `ByteArray.uset`
  (in place, no bounds check);
* previous pixel = four `UInt8` loop arguments; index = 256-byte `ByteArray`; runs = `fill` loop;
* header parsed with `b[i]` (proofs from `22 ≤ size`);
* `b.size < USize.size` is not provable for a `ByteArray` in the logic, so `decodeRGBA` tests it and falls back
  to the spec (`slowPath`) otherwise: dead code in practice, but the theorem stays unconditional.

MPx/s: testcard 371 (qoi.h 752), kodim10 102 (168), synth_photo 92 (97), synth_flat 243 (342).

### Experiments between v1 and v2 (all unproven prototypes, measured, kept or reverted)
| variant | change | result |
|---|---|---|
| A | index as `Array UInt32` of packed pixels (1 `Array.uset` per pixel instead of 4 `ByteArray.uset`) | **+16 %** (0.632 → 0.736x interleaved). kept |
| A2 | INDEX op stores the fetched entry instead of re-packing it | ±0 (noise). kept (simpler) |
| B | previous pixel packed in one `UInt32` (unpack per use) | **−7 %**. reverted |
| C | `o`/`oe` (output offset/end) instead of a pixel counter `k` | ±0. kept (one fewer loop-carried value) |
| D | loop arguments reordered so the per-step ones are passed in registers | ±0. kept |
| E | B + bytes extracted from the packed pixel at store time | worse (87 vs 83 instr/px). reverted |
| F | dispatch order of qoi.h (`=0xFE`, `=0xFF`, `<0x40`, `<0x80`, `<0xC0`, run) instead of a top-bit split | branch misses/px kodim10 0.55 → 0.45, synth_photo 0.62 → 0.48 (now equal to qoi.h). kept |
| F2 | `fill` takes the run pixel packed (4 live values fit callee-saved registers) | ~−2 % cycles on run-heavy images. kept |

### v2 = F2, proven (≈0.74x)

### Run pattern (v3, proven, 0.87–0.90x)
Runs are 75–95 % of the pixels of edgecase, qoi_logo, testcard(_rgba), dice, synth_flat, and `fill` costs
~17 instructions per pixel (4 byte stores, each with its own `lean_is_exclusive` check). Copying `out` into itself
with `copySlice` is impossible (the same object would be passed owned and borrowed → refcount 2 → full copy),
so the decoder keeps a separate 256-byte *pattern*: 64 copies of the last long run's pixel, of which the first
`pl` are valid.
* G: pattern rebuilt (64-pixel `fill`) on every long-run miss: edgecase 8.1 → 3.8 cycles/px, but testcard
  10 → 20 (thrashing). reverted.
* H: on a miss, write the run with `fill` and then `copySlice` the bytes just written into the pattern (cheap
  `memcpy`, no rebuild); on a hit (same pixel, `n ≤ pl`) one `copySlice` pattern → output.
  Threshold 8/16/24 px all within noise; 16 chosen (H16 = v3). Per-pixel instructions: edgecase 29.7 → 14.6,
  dice 38 → 26, synth_flat 34.6 → 28.9, testcard 36.4 → 35.4, photos +2 (more loop state).
* I: separate thresholds for hits (4 or 8) and refreshes (16 or 24): ≤ 5 %, within noise, not worth another
  proof case. reverted.

### Ideas measured or analysed and rejected
* Writing 4 output bytes at once: impossible with core `ByteArray` (no 32-bit store primitive); `FloatArray`
  stores 8 bytes but `Float.ofBits`/`toBits` cannot be reasoned about in the logic.
* Avoiding the zero-fill in `alloc`: there is no primitive that sets a `ByteArray`'s size without writing it.
  The fill is a `memcpy` (≈ 5–7 % of time on the 16.8 Mpx images, < 2 % elsewhere). A scratch-buffer design
  (decode into an L2-resident buffer, append with `copySlice`) would avoid it but complicates the loop/proof.
* `push`-based output: `lean_byte_array_push` is an out-of-line call per byte — far slower than `uset`.

## Why the Lean version is still slower than qoi.h on photos/runs (what the compiler/runtime made hard)
* **Every byte store carries a uniqueness check.** `ByteArray.uset` compiles to
  `if (lean_is_exclusive(a)) r = a; else r = lean_copy_byte_array(a); r->data[i] = v;`. The store is through a
  `uint8_t*`, which may alias the object header, so gcc must reload `m_rc` before *every* store: 4 checks per
  output pixel (qoi.h: 4 plain stores that gcc can merge). Plus the `Array.uset` on the index checks uniqueness
  and runs `lean_dec` on the old element (a scalar, but the C code cannot know).
* **The never-taken copy calls cost registers.** Values live across the (cold) `lean_copy_byte_array` calls
  must sit in the 5 callee-saved registers or be spilled; with 11+ loop-carried values gcc keeps the previous
  pixel's bytes in stack slots, putting store-to-load forwarding on the pixel → pixel dependency chain.
  Result: ~83 instructions per photo pixel vs 62 for qoi.h, same branch-miss rate.
* Boxed scalars in `Array UInt32`: each index read is `lean_inc`/`lean_dec` of a scalar box (two predictable
  branches), each write tests the old element.
* No way to give gcc branch-probability hints or to merge stores from Lean source.

## Proof strategy and what was painful
One refinement step (no intermediate model): `loop_eq` states that, for any `I` related to `idx`,
`loop … = (Spec.pixels ((oe - o) / 4) I ⟨pr,pg,pb,pa⟩ (rest b e pos)).map (fun ps => ⟨out[0:o] ++ rgbaL ps⟩)`,
proved by `fun_induction loop` (13 cases: 6 opcodes, 3 cut-off chunks, 3 run variants, 2 exits). Every case is
"compute the chunk on a cons-list (`rest_succ`), apply the matching `chunk_*` lemma, use `single_step`/`run_step`/
`none_step`, rewrite the IH". Tag-range facts are `UInt8 → Nat` + `omega` (`u8_arith`); `USize` facts go through a
`usize_arith` macro (case on 32/64-bit `numBits`, push `toNat` through, `omega`) or small lemmas
(`toNat_add_lit`, `toNat_add_4mul`, …). The header is handled by `decode_cons`, a closed form of `Spec.decode` on
a 14-byte cons prefix, proved through the match splitter.

Re-proving after each optimisation was cheap: going from v1 to v2 (different index representation, different
dispatch order, `o`/`oe` instead of `k`, new argument order) all 11 loop cases went through on the first attempt
once the building-block lemmas (`IdxRel.set/get`, `unpack_pk`, `take_fill`) were replaced; v3's three run cases
needed two `copySlice` lemmas (`take_copy_hit`, `take_copy_pat`). Most time went into tooling problems:
* `simp … at *` silently skips hypotheses that later `let`s/proofs depend on, so the generic arithmetic tactic
  failed inside the loop body; fixed with `clear_value *` first. Inside the proof (big contexts containing the IH)
  it was also slow (whnf timeouts), so the proof uses the small lemmas above + `omega` instead.
* `omega` treats `(pos + OfNat.ofNat 1).toNat` and `(pos + 1).toNat` as different atoms; `have`s need explicit
  types. `x / (4 % 2^64)` is not linear for omega until `Nat.reduceMod` runs.
* Kernel blow-ups (each costing a 2+ minute failed check): evaluating the spec's header `match` on literal bytes
  (`obtain ⟨rfl, …⟩` + `simp [decode]`) made the kernel die with "deep recursion" after 155 s — going through
  `split` on the match (the generated splitter) is instant; `generalize … at *` over a goal containing the
  implementation's proof terms produced a term the kernel needed 2 min to reject — replaced by a quantified lemma;
  `decide` on a 256-element list hit max recursion — replaced by `List.flatten_replicate_replicate`.
* Termination proofs: `decreasing_by` goals mention `b.uget pos ⋯` where the bound hypothesis mentions the `let`
  name `tag`; needed standalone lemmas (`run_dec`) instead of inline arithmetic.
* `bench/fuzz.py` itself crashes for some seeds with `--n` ≥ ~5000 (`randrange(14, len(b)+1)` after a mutation
  truncated the file below 14 bytes, line ~61). I did not edit it; the 20 000-case run used a patched copy
  (`elif len(b) >= 14:`).

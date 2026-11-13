# QOI decoders: simple Zig vs. optimized Zig vs. proven-correct Lean

A proof-of-concept comparing four ways to decode the [Quite OK Image Format](https://qoiformat.org/):

| decoder | what it is | size | correctness evidence |
|---|---|---|---|
| **zig-simple** | the straightforward conceptual decoder ([`zig/src/simple.zig`](zig/src/simple.zig)) | 90 lines | correct on valid files; no input validation by design |
| **zig-fast** | a hand-optimized Zig decoder ([`zig/src/fast.zig`](zig/src/fast.zig)) | 300 lines | 20 000-case differential fuzz against the spec, 0 mismatches |
| **lean-spec** | a short, readable Lean 4 *specification* that also runs ([`lean/QOI/Spec.lean`](lean/QOI/Spec.lean)) | 103 lines | it *is* the definition |
| **lean-fast** | an optimized Lean 4 decoder ([`Impl.lean`](lean/QOI/Fast/Impl.lean)) with a **machine-checked proof** that it returns exactly what the spec returns, on every input ([`Proof.lean`](lean/QOI/Fast/Proof.lean)) | 275 + 637 lines | `theorem decodeRGBA_eq_spec`, axioms: `propext, Classical.choice, Quot.sound` |

`qoi.h`, the reference C implementation, is the yardstick. The two optimized versions were developed in parallel, as
a race to see which could be made faster.

## Results

Ryzen 7 5700G (Zen 3), one pinned core, median of ≥ 2 s of repeated decodes per cell, output allocation included.
Higher is better (megapixels per second).

| image | Mpx | qoi.h (C) | zig-simple | **zig-fast** | **lean-fast** (proven) |
|---|---:|---:|---:|---:|---:|
| edgecase | 0.02 | 884 | 1128 | **3040** | 1234 |
| qoi_logo | 0.10 | 921 | 1603 | **5095** | 699 |
| testcard | 0.07 | 742 | 804 | **1800** | 465 |
| testcard_rgba | 0.07 | 750 | 806 | **1852** | 467 |
| dice | 0.48 | 496 | 571 | **1580** | 493 |
| kodim10 | 0.39 | 174 | 153 | **473** | 143 |
| kodim23 | 0.39 | 173 | 155 | **476** | 143 |
| wikipedia_008 | 0.99 | 153 | 147 | **467** | 124 |
| synth_flat | 16.78 | 351 | 382 | **489** | 474 |
| synth_photo | 16.78 | 131 | 120 | **245** | 133 |
| **geomean vs qoi.h** | | 1.00× | 1.08× | **2.71×** | 0.89× |

The executable spec runs at **0.017×** qoi.h (5–11 MPx/s; lists of bytes and lists of pixels). The proven decoder is
**~52× faster than the spec it is proven equal to**, and on par with `qoi.h` (faster on 3 of 10 images).

**The race went to Zig, by about 3×.** The optimized Zig decoder is 2.7× faster than `qoi.h` overall, 2.7–3× on the real
photos and 1.9× on the synthetic one. The proven Lean decoder reaches 0.9× `qoi.h`. The gap comes from what each language lets you *express*,
not from the proof: Lean's proof was cheap to redo after each optimization, but the Lean runtime has no way to
write a 32-bit pixel or skip a uniqueness check on a byte write (details below).

Raw output: [`results/bench.txt`](results/bench.txt), [`results/bench.json`](results/bench.json). The test images are
the official [QOI test suite](https://qoiformat.org/qoi_test_images.zip) plus two generated 4096×4096 images
([`ref/gen.c`](ref/gen.c)): a noisy gradient "photo" (DIFF/LUMA/RGB-heavy) and a flat UI-like RGBA image
(95 % of pixels come from runs).

## The code

### The simple decoder

[`zig/src/simple.zig`](zig/src/simple.zig) is the 60-line function you'd write on a whiteboard: a `switch` on the
tag byte, a `@memset` per run, and an index update per chunk. It does not check its input. It is about 10 % slower
than `qoi.h` on photos and faster on run-heavy images, where one `@memset` per run pays off (1.08× overall).

### The specification

[`lean/QOI/Spec.lean`](lean/QOI/Spec.lean) is written to be read. Bytes are a `List UInt8`, and each chunk type is
one pattern match:

```lean
def chunk (index : Vector Pixel 64) (prev : Pixel) : List UInt8 → Option (Pixel × Nat × List UInt8)
  | [] => none
  | tag :: rest =>
    if tag = 0xFE then                                   -- QOI_OP_RGB
      match rest with
      | r :: g :: b :: rest => some ({ prev with r, g, b }, 0, rest)
      | _ => none
    else if tag = 0xFF then ...                          -- QOI_OP_RGBA
    else if tag >>> 6 = 0 then                           -- QOI_OP_INDEX
      some (index[tag.toNat % 64]'(Nat.mod_lt _ (by decide)), 0, rest)
    else if tag >>> 6 = 1 then                           -- QOI_OP_DIFF: three 2-bit deltas, bias 2
      some ({ prev with r := prev.r + (tag >>> 4 &&& 3) - 2
                        g := prev.g + (tag >>> 2 &&& 3) - 2
                        b := prev.b + (tag &&& 3) - 2 }, 0, rest)
    else if tag >>> 6 = 2 then ...                       -- QOI_OP_LUMA
    else                                                 -- QOI_OP_RUN: bias 1
      some (prev, (tag &&& 63).toNat, rest)

def pixels (n : Nat) (index : Vector Pixel 64) (prev : Pixel) (bytes : List UInt8) : Option (List Pixel) :=
  match n with
  | 0 => some []
  | n + 1 => do
    let (px, extra, rest) ← chunk index prev bytes
    let extra := min extra n
    let more ← pixels (n - extra) (index.set px.hash px) px rest
    return List.replicate (extra + 1) px ++ more
```

It pins down what `qoi.h` leaves implicit: which inputs are *rejected* (bad header, more than 400 M pixels,
a chunk that runs into the 8-byte end marker, running out of chunks), and that an over-long run is cut short. On valid
files it is byte-identical to `qoi.h`. The full rules are in [`bench/PROTOCOL.md`](bench/PROTOCOL.md). Because it
runs, it doubles as the **fuzzing oracle** for both optimized decoders.

### The proven Lean decoder

[`lean/QOI/Fast/Impl.lean`](lean/QOI/Fast/Impl.lean) is plain Lean, with no `extern`, `implemented_by`, `unsafe` or
`partial`. It is a single tail-recursive `loop` (compiled to a C loop) over a `ByteArray`. Every array access carries
a proof that the index is in bounds, and the compiler erases the proof, so no runtime check remains:

```lean
    else if h80 : tag < 0x80 then
      -- QOI_OP_DIFF
      let r := pr + (tag >>> 4 &&& 3) - 2
      let g := pg + (tag >>> 2 &&& 3) - 2
      let bl := pb + (tag &&& 3) - 2
      loop r g bl pa (pos + 1) (o + 4)
        (idx.uset (hashIdx r g bl pa) (pk r g bl pa) (by have := hashIdx_lt r g bl pa; omega))
        (put4 out o r g bl pa (by usize_arith) hs) b e oe pat pp pl he hbs (by simp [hidx]) hpat
        (by rw [size_put4]; exact hs) (by usize_arith) (by rw [size_put4]; exact hoe) (by usize_arith)
```

and [`lean/QOI/Fast.lean`](lean/QOI/Fast.lean) states the result, which is checked on every `lake build`:

```lean
theorem QOI.Fast.decodeRGBA_eq_spec (b : ByteArray) :
    decodeRGBA b = (QOI.Spec.decode b.toList).map (fun img => ⟨img.rgba.toArray⟩)
-- 'QOI.Fast.decodeRGBA_eq_spec' depends on axioms: [propext, Classical.choice, Quot.sound]
```

The theorem is equality of `Option`s, so it covers rejection too. It needs no hypotheses: Lean cannot prove that an
in-memory array's size fits in a machine word, so `decodeRGBA` checks this at run time and falls back to the spec
(the fallback never runs in practice).

What made it fast (log: [`lean/NOTES.md`](lean/NOTES.md)):

| step | effect |
|---|---|
| v1: one tail-recursive loop, `USize` positions, proof-erased `uget`/`uset`, output allocated once, previous pixel as 4 unboxed `UInt8` arguments | 40× → **0.61×** qoi.h |
| index as `Array UInt32` (one store per pixel instead of four) | +16 % |
| `qoi.h`'s opcode test order | branch misses/px 0.55 → 0.45 on kodim10 |
| v3: long runs (≥ 16 px) copied with one `ByteArray.copySlice` from a cached 256-byte pattern of the last run's pixel | 0.74× → **0.89×** |

**The proof** ([`Proof.lean`](lean/QOI/Fast/Proof.lean), 49 lemmas) is a single induction over `loop` (13 cases: six
opcodes, three cut-off chunks, three kinds of run, and the exit). It shows that the loop's output equals the bytes
already written followed by `rgba (Spec.pixels …)` of the remaining input, with the index related to the spec's
`Vector`. It uses core Lean only (`omega`, `simp`, `fun_induction`; no Mathlib, and no `bv_decide`, which relies on
`native_decide`). Re-proving after each optimization was cheap: after the v1 → v2 rewrite, every loop case went
through on the first try. Most of the effort went into kernel/elaborator traps (e.g. unfolding the spec's header `match`
on literal bytes ran the kernel for 155 s before it failed; going through the match splitter is instant). A clean build
including the proof takes about 15–45 s.

**Why it stops at ~0.9× qoi.h:** every `ByteArray.uset` checks that the array is not shared (`lean_is_exclusive`)
before writing, and since the write goes through a `uint8_t*`, the C compiler has to reload the reference count
before *every* byte. That is 4 checks + 4 single-byte stores per pixel, where C does one 32-bit store. Core Lean has
no 32-bit store into a `ByteArray`, and no way to size one without zero-filling it. The cold copy-on-shared paths also
force values to live in callee-saved registers, so the previous pixel gets spilled onto the pixel-to-pixel dependency
chain (~83 instructions per photo pixel vs 62 for `qoi.h`).

### The optimized Zig decoder

[`zig/src/fast.zig`](zig/src/fast.zig) has a guarded fast loop with no per-chunk checks, which runs while at
least 5 input bytes and 64 output pixels remain, and a careful tail loop that checks every chunk exactly like the spec.
The fast loop is **branch-free per opcode**:

```zig
const t = tag;
const cur = w;
tag = bextr(cur, field(F_CTRL, t));          // next tag comes out of the 8-byte window already in a register
p += field(F_LEN, t);
w = readInt(u64, bytes[p..][0..8], .little);

const x = std.math.rotr(u64, cur, 8);        // payload bytes
const d = field(F_ADD, t) +% pdep(x, field(F_PMASK, t)) +% (table[LUMA + (x & 0xFF)] & field(F_LMASK, t));
var ix = index[t];
if (t == hp) { @branchHint(.cold); asm volatile ("" ::: .{ .memory = true }); ix = prev; }
const px = ((prev & field(F_KEEP, t)) | ix) +% d;   // every opcode, one formula

fill8(out, o, pack(px));                      // always store 8 pixels; runs <= 8 cost nothing extra
...
index[hp] = prev;                             // index write delayed by one chunk
hp = hash(px);
```

What made it fast (29 experiments, all with measurements in [`zig/NOTES.md`](zig/NOTES.md)):

| step | kodim10 MPx/s | gain |
|---|---:|---|
| v1: guarded fast path + careful tail, a 256-entry table turns every opcode into `((prev & keep) \| index[tag]) + delta` (photos have ~1 chunk/pixel in random order, so a `switch` mispredicts constantly) | 195 | 1.57× qoi.h |
| "spread" pixels: r,g,b,a in four 16-bit lanes of a `u64`, so per-channel wrapping add is one `add`; RGB/RGBA payloads placed with one BMI2 `pdep`; next tag extracted from the window in a register | 288 | +45 % |
| delaying the index write by one chunk (perf showed later loads stalled on the late-computed hash address). The INDEX-of-the-pending-slot case, which encoders never emit, is a cold branch, kept from becoming a `cmov` with an empty `asm volatile` | 414 | +40 % |
| fewer instructions: structure-of-arrays table, never-written index slots 64..255 double as zero padding so `index[tag]` needs no mask, one bound check per chunk | 480 | +8–13 % |

What didn't help: moving the pixel into SIMD registers (−38 %), `cmov` hazard bypass, out-of-line fixup calls
(spills), pointer cursors (−7 %), unrolling, a SIMD pre-pass that precomputes chunk lengths (correct but 15 % slower),
non-temporal stores, and huge pages (helped one image and hurt another; rejected as OS work rather than decoding work).

It ends at ~9.5 cycles per chunk on photos, against a measured ~6.6-cycle floor for the bare parse chain, with the
integer schedulers full. `synth_flat` sits at the floor of faulting in and filling 67 MB of fresh memory: two thirds of
its time is kernel page faults, which every decoder pays.

## Correctness and trust

* **lean-fast**: the theorem above, checked by Lean's kernel. The trusted base is the Lean kernel, the Lean compiler
  and its C runtime primitives (`ByteArray.uget/uset/copySlice`, `Array.uset`, fixed-width integers), and the C
  compiler. The spec itself is the other thing you have to trust: it is 100 lines and agrees with `qoi.h` on every
  test image.
* **zig-fast**: no proof. [`bench/fuzz.py`](bench/fuzz.py) compares it with the compiled spec on random chunk streams
  (biased to each opcode and to cut-off chunks), mutated and truncated real files, and broken or extreme headers
  (`0`, `2^32-1`, width·height overflow). Final run: 20 000 cases, about half accepted and half rejected,
  **0 mismatches** for both zig-fast and lean-fast. [`bench/run.py`](bench/run.py) also checks every benchmark
  output's hash against `qoi.h`.
* **zig-simple** is only compared on valid files; malformed input makes it crash, as its doc comment warns.

## Caveats

* One machine (Zen 3), one core, one compiler version each: Zig 0.16.0 (LLVM), Lean 4.34.1 → gcc 16.2 `-O3
  -march=znver3`, `qoi.h` with gcc 16.2 `-O3 -march=native`. Zig uses BMI1/BMI2 (`pdep`, `bextr`) on this target;
  without them it falls back to portable code (also fuzzed clean).
* The development benchmarks in the NOTES files ran on a shared, busy machine (both optimizers ran at once, on
  different cores). The table above is a final run on an idle machine. Expect ±5 % run to run.
* The large synthetic images are dominated by page faults on the fresh 67 MB output buffer. That is real cost
  (`qoi.h` pays it too), but it compresses the differences between decoders.
* Both optimized decoders were written by AI agents working in parallel under matching rules and a similar time budget
  (about 2¼ hours each). The Zig side ran 29 logged experiments; the Lean side went through 3 proven versions and
  about a dozen measured prototypes.

## Reproduce

```sh
nix-shell                      # zig 0.16, lean 4.34 (lake), gcc, python3; see shell.nix
./setup.sh                     # downloads test images, builds everything, generates synthetic images
python3 bench/run.py --cpu 4   # the results table
python3 bench/run.py --cpu 4 --only c-qoi.h,lean-spec --images testcard,kodim10
python3 bench/fuzz.py --n 20000
```

Every decoder speaks the same CLI (`decode in.qoi out.rgba` / `bench in.qoi iters`); see
[`bench/PROTOCOL.md`](bench/PROTOCOL.md).

## Layout

```
zig/src/simple.zig        conceptual decoder        zig/src/fast.zig      optimized decoder
zig/src/cli.zig           shared Zig CLI driver     zig/NOTES.md          Zig optimization log
lean/QOI/Spec.lean        the specification         lean/QOI/Fast/Impl.lean   optimized decoder
lean/QOI/Fast/Proof.lean  proof Impl = Spec         lean/QOI/Fast.lean    the theorem + #print axioms
lean/NOTES.md             Lean optimization + proof log
ref/qoi.h                 reference implementation (MIT, © Dominic Szablewski), ref/qoi_ref.c wraps it
ref/gen.c                 synthetic image generator bench/  run.py, fuzz.py, PROTOCOL.md
```

# zig-fast: optimization log

Machine: Ryzen 7 5700G (Zen 3), pinned to one core, zig 0.16.0 `--release=fast -Dcpu=native`.
The machine was shared with other jobs (load average ~10, every core ~75% busy during this
work), so single runs swing by 10-30%. A/B comparisons below were made by running the variants
interleaved, 3-5 rounds, taking the best per-variant time (a `/tmp`-local script, not committed);
the headline table at the bottom is `bench/run.py --cpu 4`. Where I quote cycles or instruction
counts they come from `perf stat -e cycles:u,instructions:u` (user-mode counters work here).

Numbers are MPx/s. "photo" = kodim10 / kodim23 / wikipedia_008 / synth_photo (~1 chunk per pixel,
mostly LUMA/DIFF/INDEX, very unpredictable opcode sequence). "flat" = synth_flat (95% of pixels
from runs, 40% of chunks are RUN, 39% INDEX).

Opcode mix (from a quick stats script over testdata/):

| image | chunks/px | INDEX | DIFF | LUMA | RGB | RGBA | RUN | px from runs |
|---|---|---|---|---|---|---|---|---|
| kodim10 | 0.98 | 22% | 9% | 56% | 4% | 0 | 8% | 10% |
| wikipedia_008 | 1.00 | 28% | 28% | 34% | 7% | 0 | 4% | 4% |
| synth_photo | 1.00 | 12% | 17% | 48% | 21% | 0 | 2% | 2% |
| dice | 0.28 | 3% | 10% | 7% | 1% | 68% | 12% | 75% |
| synth_flat | 0.08 | 39% | 0 | 0 | 18% | 4% | 40% | 95% |

Baseline (same session): qoi.h ~170 kodim, ~150 wikipedia, ~131 synth_photo, ~355 synth_flat;
zig-simple ~1.0x qoi.h geomean.

## Structure that stayed fixed from v1 on

* Header checks exactly as the spec; `width*height` computed in u64 and compared against
  400 000 000 before allocating (no overflow possible: both factors < 2^32).
* **Guarded fast path + careful tail.** The fast loop runs only while at least 5 chunk bytes
  remain (the largest chunk) and at least 64 output pixels remain (longest run 62, rounded up to
  whole 8-pixel vector stores). Under those conditions every chunk is complete, every 8-byte input
  load `bytes[p..p+8]` is in bounds (p <= end = len-8), and every 32-byte output store is in
  bounds, so the loop has no per-chunk checks. The last few chunks/pixels go through a
  straightforward tail loop that checks every chunk against `end`, truncates runs to the missing
  pixel count, and rejects on running out of chunks: exactly the spec.
* **Branch-free chunk decoding via a 256-entry table** indexed by the tag byte: every chunk type
  is expressed as `px = ((prev & keep) | index[tag]) + delta(payload)` (v1-v13 also masked the
  index value; v14 made that unnecessary), plus a length
  and a pixel count. Photo images have ~1 chunk per pixel with an essentially random opcode
  sequence, so any switch on the opcode mispredicts constantly; qoi.h's `if` chain does exactly
  that.
* **Runs as overlapping 32-byte stores**: every chunk stores 8 copies of its pixel at `out+o`
  and then advances `o` by its count (1 for non-runs), so a run of <= 8 costs nothing extra and a
  longer run is 7 more stores behind a rarely-taken branch.

## Attempts

(MPx/s; kodim = kodim10, wiki = wikipedia_008, sp = synth_photo, flat = synth_flat.)

1. **v1: SWAR on packed RGBA u32 + table.** Bytewise add as `((x&0x7f7f7f7f)+(y&0x7f7f7f7f)) ^
   ((x^y)&0x80808080)`; INDEX chosen by a (predictable-ish) branch. kodim ~195, wiki ~146,
   sp ~152, flat ~413, dice ~834. **1.57x qoi.h geomean.** Kept as the starting point.
2. **Branch-free INDEX select** (always load `index[tag&63]`, select by mask): +2..5% on photos,
   within noise elsewhere. Kept.
3. **v2: "spread" pixels + shift-window parsing.** Keep each pixel as r,g,b,a in the low byte of
   four 16-bit lanes of a u64; lane-wise mod-256 add is then one plain `add` (the high byte of a
   lane absorbs the carry). The payload bytes are spread into lanes with BMI2 `pdep`. The next
   tag is taken from the 8-byte window already in a register (`w >> 8*len`), so finding the next
   chunk is shift arithmetic, not a dependent byte load. kodim 195 -> **288**, wiki 146 -> 287,
   sp 152 -> 193, dice 834 -> 920. **1.87x.** Kept.
4. **v3: pixel in an xmm register** (`@Vector(4,u8)` arithmetic, hash via `pmaddubsw`/`pmaddwd`).
   kodim 288 -> 178, everything slower. The GPR<->vector moves and the 2x 3-5 cycle multiply-add
   chain for the hash sit on the loop-carried path. Reverted.
5. **v4: delay index writes by 2 chunks, bypass pending ones with cmov.** kodim 288 -> 240.
   The bypass compare (`slot == hash(last pixel)`) put the hash *into* the critical path. Reverted
   (but see 9-11: the idea was right, the bypass was wrong).
6. **v5: cheaper per-chunk work**: no mask in the hash (lanes are < 1024, so lane partial
   products never carry into the next lane and the extra multiples of 256 vanish mod 64), LUMA
   nibbles from a 256-entry table, one counted inner loop instead of two bound checks per chunk.
   64 -> 54 instructions per chunk, speed unchanged (+1%). That told me the loop was latency-bound,
   not throughput-bound. Kept (smaller).
7. **v6: table-driven parse step + fewer ops**: the next tag is `bextr(w, ctrl[tag])` (one table
   load + one 1-cycle bextr instead of a compare/cmov length computation + shift + movzx), the
   pdep mask comes straight from memory (`pdep r, r, m64`), the hash constant is pre-shifted so
   the slot is just `imul; shr 58`. 54 -> 35 instructions/chunk, but still ~16 cycles/chunk:
   kodim 288 -> 290, wiki 286 -> 300, dice 980 -> 1100. **~+4% geomean**. Kept.
8. **Diagnosis with deliberately-wrong variants** (timing only): storing the index at an address
   known early (`index[tag&63] = px`) gave kodim 285 -> 364; dropping the index store gave 391.
   So the bottleneck was the index *store address*: `hash(px)` is computed late (px -> imul ->
   shr), and later loads (the table and the INDEX load) wait on it.
9. **v7: delay the index write by 2 chunks; a pending-slot hit is a cold branch.** An INDEX chunk
   naming a slot whose write is still pending must see the pending pixel. Encoder output never
   does that (INDEX of the previous pixel would be a RUN), so it is handled by an unlikely branch
   instead of a cmov. kodim 291 -> 338, wiki 298 -> 336, sp 183 -> 208. Kept, but LLVM
   if-converted part of the "cold" branch back into a cmov.
10. **v8: same with a `noinline` fixup function (to stop if-conversion), delay 1/2/3.** delay 1:
   kodim 388, wiki 383 (+12% over v7); delay 2: 334; delay 3: 259 (register pressure: the queue
   plus the call's clobbers spilled the window and the counter to the stack every iteration).
   Kept delay 1.
11. **v9: cold branch kept a branch with an empty `asm volatile` (no call), `prev` doubles as the
   pending value, one flat table.** No more spills: kodim 372 -> 414, wiki 367 -> 409, dice
   1226 -> 1380 (+11%). 40 instr/chunk, 12 cycles/chunk. Kept.
12. **v10: structure-of-arrays table** (field f of tag t at `[f*256+t]`, so every field is
   `base + disp + t*8`, no `shl` on the tag chain): +1..2% (noise level). Kept (harmless).
13. **madvise(MADV_HUGEPAGE) / MADV_POPULATE_WRITE on the output.** For the 16.7 Mpx images the
   67 MB output is fresh mmap memory each decode, and the 16k page faults (~1.7 us each here)
   are ~2/3 of synth_flat's time and ~1/3 of synth_photo's. Huge pages: sp 223 -> 296 but flat
   477 -> 279 (and very noisy - THP allocation/compaction on a busy machine); POPULATE_WRITE: sp
   +4%, flat +11%. Rejected: unreliable, OS-specific, and it is not decoder work (qoi.h and the
   Lean decoder pay the same page faults).
14. **v11: delay 2 with the asm-guarded branch**: no gain over delay 1 (the index chain is no
   longer the limit). Reverted.
15. **v12: 256-entry index read as `index[tag]`** (drops the `& 63`): within noise alone.
16. **v13: parse-chain loads first in program order** (so they don't queue behind the pixel
   loads on the 3 load ports): no change. Kept (harmless).
17. **Parse-only loop** (tags, lengths, window reloads; no pixels): ~6.6 cycles/chunk = ~670
   MPx/s on kodim. A latency microbenchmark here shows 4-cycle loads with simple addressing,
   5 cycles with a scaled index, so the parse chain is `ctrl load (5) + bextr (1)` per chunk,
   and the window chain `len load (5) + add + window load (5) + bextr` per 2 chunks: both ~6.
   The full loop was ~10.5 cycles at IPC ~3.6, i.e. now limited by the number of instructions
   competing with the parse chain.
18. **v14: fewer instructions**: index[64..256] are kept zero forever (scratch slot moved to 256)
   so `index[tag]` needs no mask *and* no `& imask` (non-INDEX tags read 0 and OR it away), and
   the inner loop runs `while (p <= p_blk)` (one fused cmp/jcc instead of a counter). 38 -> 34
   instructions: kodim 438 -> 480, wiki 426 -> 471, dice 1451 -> 1641, testcard 1683 -> 1786
   (**+8..13%**). Kept.
19. **v15: pointer cursors** for input and output (frees two base registers, simple addressing
   for the window load): kodim 482 -> 447, wiki 475 -> 437 (-7%, reproduced twice). The
   generated loop moved the run block and lost a folded load; I did not chase it. Reverted.
20. **LUMA nibbles via `luma[x & sel[tag]]`** (sel = 0xFF for LUMA, 0 otherwise; luma[0] = 0),
   dropping the movzx + mask load + AND: -1 instruction but kodim 482 -> 457 (-5%). The LUMA
   value now waits for a dependent pair of loads, and pixel latency still matters (through the
   delayed index store address). Reverted.
21. **Delay 2 again on top of v14** (asm-guarded branch): 648 -> 639 geomean. Reverted.
22. **Three more instruction trims** (`rorx` for the payload word; the hash constant as an
   imul memory operand; DIFF/LUMA deltas pre-stored in the never-written index slots 64..255 so
   one `index[tag]` load supplies them): each within +-1%. Only `rorx` actually reduced the count
   (LLVM undid the other two). Kept `rorx` (harmless).
23. **Diagnosis: two-pass split** (pass 1 records chunk positions for a block, pass 2 decodes
   from them). Parse-only runs at ~6.7 cycles/chunk (= the analytic chain); decode-only at ~10
   cycles/chunk with ~43 instructions (IPC ~4.3) - and removing any one of its suspected chains
   (prev, index load, index store, output store) changes it by < 5%. Integer-scheduler
   dispatch stalls (`de_dis_dispatch_token_stalls2.int_sch{0,1,2}`) were ~2.3 cycles/chunk,
   scheduler 3 (no AGU) ~0: the per-chunk work all hangs off the tag and fills the schedulers.
24. **v19: unroll by 2** (LLVM can alternate registers instead of 4 rotation `mov`s per chunk):
   36.3 -> 33.4 instructions/chunk, cycles unchanged (9.8 -> 9.7). Within noise; not kept
   (simpler without).
25. **v20/v21: read the payload backwards from the chunk end.** Load the 8 bytes ending at the
   chunk's last byte big-endian (`movbe`) and store pixels as (a, b, g, r) lanes: then a single
   per-tag `pdep` mask handles RGBA (a,b,g,r -> lanes 0..3), RGB (b,g,r -> lanes 1..3) *and*
   LUMA (low nibble -> b lane, high nibble -> r lane), with no LUMA table, no mask load, no
   shr/movzx/and. 33.4 -> 29.5 instructions/chunk, but the same ~9.8 cycles: the payload load
   now hangs off `p += len`, lengthening the tag -> pixel latency (v21 moves it off that chain
   with a per-tag shift: same speed again). Over 8 interleaved rounds v20 vs v14: kodim/wiki
   -2..4%, dice/synth_photo +1..3%, i.e. a tie. Not kept (v14's loop is a bit faster on the
   photo images that matter most), but it is the neatest trick in this log.
26. **Strip-down diagnostics on v20** (cycles/chunk, kodim10; baseline 9.8-10.6 across runs): without output stores 9.9, without index
   stores 9.0, without both 7.85, everything memory-related gone 7.9 (24 instr). So the two
   stores together cost ~2.8 cycles/chunk, more than either alone; storing the index at an
   early-known address (wrong output) saves 0.7 of that. Delay 2 on v20: +5 instructions,
   slower.
27. **v23-v26: break the parse chain with a SIMD pre-pass.** For each block of 2 KiB of input,
   compute with AVX2 `len[i]` (length if byte i were a tag) and `len2[i] = len[i] +
   len[i + len[i]]` (two chunks), then advance two chunks per dependent byte load
   (`p += len2[p]`, ~7 cycles per 2 chunks instead of ~6 per chunk). Correct (fuzzed), but:
   v23 39 cycles/px (reading bytes out of 32-byte vector stores that have not committed yet
   cannot be store-forwarded: 1.6 `stli` events/px); v24 (double-buffered blocks, pre-pass for
   block j+1 runs before block j is decoded) 11.5; v25 (decoder state struct had kept the
   scalars on the stack because the index array lived inside it) 11.5; v26 (interleaved u16
   len|len2, pre-biased pointer) 11.8. The pre-pass alone is ~20% of the time and the decode
   loop was still ~9.4 cycles/chunk - which, with 23-26, says the parse chain was *not* the
   binding constraint any more. Abandoned.
28. **Run fill: always store 16 pixels, branch only for runs > 16** (testcard's most common
   run length is 8-15, so `cnt > 8` is a coin flip there): no gain on testcard, -1..2%
   elsewhere. Reverted.
29. **Non-temporal output stores** (microbenchmark only): writing 64 MB to freshly malloc'd
   memory here costs ~35 ms with plain 32-byte stores, ~40 ms with `vmovntdq`, ~42 ms with our
   overlapping 4-byte-step stores. synth_flat decodes in ~34 ms, i.e. it is at the "fault in
   and fill the output" floor (two thirds of its time is kernel page-fault work; see 13).
   Nothing left to win there in user space.

### Things that never helped (summary)

* Anything that moved the pixel into vector registers (3), cmov-based hazard handling (5),
  out-of-line fixup calls (spills, 10), deeper index-write delays (11, 21, 26), pointer cursors
  (15), unrolling (24), and the SIMD length pre-pass (27).
* Instruction count stopped mattering at ~34/chunk: 29.5 (v20) and 36 (v14) run at the same
  ~9.5-9.8 cycles/chunk on kodim; perf shows IPC ~3-3.8 with the integer schedulers full.

## Final version (zig/src/fast.zig = v14 + rorx, cleaned up)

Hot loop: ~35 instructions and ~9.5 cycles per chunk on kodim10 (~1 chunk per pixel), against
a measured ~6.6-cycle floor for the bare parse chain. One spec-equivalent addition at the end:
reject before allocating if even 62 pixels per remaining byte cannot reach width*height (the
spec would run out of chunks anyway), so a 30-byte file cannot ask for 1.6 GB.

What mattered most (kodim10, MPx/s):

| step | kodim10 | photo effect |
|---|---|---|
| v1 branch-free table + SWAR u32 + guarded fast path | ~195 | 1.57x qoi.h geomean |
| spread u64 lanes + pdep + next tag from the window (v2) | ~288 | +45% |
| delayed index write + cold-branch hazard, asm barrier (v7-v9) | ~414 | +40% |
| SoA table, no imask, one bound check per chunk (v10-v14) | ~480 | +15% |

Correctness: `fuzz.py --only zig-fast --n 20000 --seed 20261113`: 0 mismatches (9901
accepted / 10099 rejected by the spec). Note: `bench/fuzz.py` itself crashes on some seeds
(`r.randrange(14, len(b) + 1)` after a truncation below 13 bytes); the run above used a local
copy that differs only in that line (`randrange(min(14, len(b)), ...)`) and its ROOT path. A
baseline-CPU build (portable pdep/bextr fallbacks, no BMI) also fuzzed clean (800 cases).

Final `python3 bench/run.py --cpu 4 --only c-qoi.h,zig-simple,zig-fast --seconds 0.5`
(shared machine, two consecutive runs gave 2.707x and 2.692x):

```
image              Mpx       c-qoi.h    zig-simple      zig-fast   (median MPx/s)
edgecase          0.02         865.7        1105.8        2951.5
qoi_logo          0.10         951.2        1600.6        5126.4
testcard          0.07         768.3         798.1        1781.0
testcard_rgba     0.07         740.1         790.1        1810.0
dice              0.48         477.7         560.5        1556.5
kodim10           0.39         170.0         150.0         463.0
kodim23           0.39         170.5         153.3         471.6
wikipedia_008     0.99         150.9         145.8         459.7
synth_flat       16.78         352.5         381.7         495.6
synth_photo      16.78         125.4         115.0         241.5

geomean speed vs qoi.h:
  c-qoi.h      1.000x
  zig-simple   1.078x
  zig-fast     2.707x
```

# Decoder protocol

Every decoder in this repo is a standalone executable with the same interface:

```
<exe> decode <in.qoi> <out.rgba>   # write raw RGBA8 (width*height*4 bytes); on rejected input exit 1, print "invalid" to stderr
<exe> bench  <in.qoi> <iters>      # decode <iters> times in-process; print "<min_ns> <median_ns> <fnv1a64-hex of RGBA output>"
```

Timing covers exactly one call of the decode function, *including* allocating the output buffer, and nothing else
(file I/O and hashing are outside the timed region). `qoi.h` mallocs its output the same way.

## Semantics

`lean/QOI/Spec.lean` is the normative definition. In words:

* header: `"qoif"`, width and height big-endian u32, channels ∈ {3,4}, colorspace ∈ {0,1}, width·height ≤ 400 000 000;
  anything else is rejected;
* the file must be at least 14 + 8 bytes; the last 8 bytes are the end marker and are *not* inspected;
* chunks are read only from `bytes[14 .. len-8]`; a chunk whose bytes do not all lie in that range is rejected,
  as is running out of chunks before width·height pixels have been produced;
* a run longer than the number of pixels still missing is truncated; bytes left over after the last pixel are ignored;
* the output is always RGBA, independent of `channels`. Initial previous pixel is (0,0,0,255); the index starts all-zero
  (0,0,0,0) and is updated with every decoded pixel.

On valid files this is byte-identical to `qoi.h` (`qoi_decode(..., 4)`). On invalid ones `qoi.h` is more lenient
(it pads with the last pixel instead of rejecting), so the fuzzer compares against the Lean spec, not `qoi.h`.

`zig/src/simple.zig` (the screenshot version) does no validation and is only required to be correct on valid files.
Every other decoder must match the spec on **all** inputs, never crash, and never read or write out of bounds.

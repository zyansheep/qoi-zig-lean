/-! Shared command-line driver for the Lean decoders (protocol: `bench/PROTOCOL.md`).
  <exe> decode <in.qoi> <out.rgba>   write raw RGBA8 pixels; exit 1 + "invalid" on rejected input
  <exe> bench  <in.qoi> <iters>      print "<min_ns> <median_ns> <fnv1a64 of RGBA hex>" -/

namespace QOI.Cli

def fnv1a (b : ByteArray) : UInt64 := Id.run do
  let mut h : UInt64 := 0xcbf29ce484222325
  for x in b do
    h := (h ^^^ x.toUInt64) * 0x100000001b3
  return h

def hex16 (x : UInt64) : String :=
  let s := String.ofList (Nat.toDigits 16 x.toNat)
  String.ofList (List.replicate (16 - s.length) '0') ++ s

/-- `decodeFn` maps the file to its RGBA bytes, or `none` if the input is rejected. -/
def run (decodeFn : ByteArray → Option ByteArray) (args : List String) : IO UInt32 := do
  match args with
  | ["decode", inp, out] =>
    let data ← IO.FS.readBinFile inp
    match decodeFn data with
    | none => IO.eprintln "invalid"; return 1
    | some px => IO.FS.writeBinFile out px; return 0
  | ["bench", inp, iters] =>
    let data ← IO.FS.readBinFile inp
    let n := iters.toNat!
    let mut times : Array Nat := #[]
    let mut last := ByteArray.empty
    for i in [0:n] do
      -- `i` is threaded through so the call cannot be hoisted out of the loop.
      let t0 ← IO.monoNanosNow
      let r := decodeFn (if i == n then ByteArray.empty else data)
      match r with
      | none => IO.eprintln "invalid"; return 1
      | some px =>
        let t1 ← IO.monoNanosNow
        times := times.push (t1 - t0)
        last := px
    let sorted := times.qsort (· < ·)
    IO.println s!"{sorted[0]!} {sorted[n / 2]!} {hex16 (fnv1a last)}"
    return 0
  | _ =>
    IO.eprintln "usage: decode <in.qoi> <out.rgba> | bench <in.qoi> <iters>"
    return 2

end QOI.Cli

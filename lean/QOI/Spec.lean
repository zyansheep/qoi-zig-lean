/-!
# QOI decoding: the specification

This file is the *meaning* of a QOI decoder, written to be read rather than run fast.
Bytes are a `List UInt8`, pixels a `List Pixel`, and every chunk is one pattern match.
`QOI/Fast.lean` holds the optimised decoder and the proof that it computes exactly this.

Semantics (shared by every decoder in the repo, see `bench/PROTOCOL.md`):
* header: `"qoif"`, width and height as big-endian u32, channels ∈ {3, 4}, colorspace ∈ {0, 1},
  width × height ≤ 400 000 000 (the limit `qoi.h` uses);
* the last 8 bytes of the file are the end marker; it must be present but is not inspected;
* chunks are read from the bytes in between; a chunk that does not fit is an error;
* a run longer than the pixels still missing is cut short;
* output is always RGBA, whatever `channels` says.
-/

namespace QOI.Spec

structure Pixel where
  r : UInt8
  g : UInt8
  b : UInt8
  a : UInt8
  deriving DecidableEq, Repr, Inhabited

/-- Slot of a pixel in the 64-entry table of recently seen pixels. -/
def Pixel.hash (p : Pixel) : Fin 64 :=
  ⟨(p.r.toNat * 3 + p.g.toNat * 5 + p.b.toNat * 7 + p.a.toNat * 11) % 64, Nat.mod_lt _ (by decide)⟩

/-- Decode one chunk. Returns the pixel it produces, how many *extra* times that pixel
repeats (only runs repeat), and the bytes after the chunk. `none` if the chunk is cut off. -/
def chunk (index : Vector Pixel 64) (prev : Pixel) : List UInt8 → Option (Pixel × Nat × List UInt8)
  | [] => none
  | tag :: rest =>
    if tag = 0xFE then                                   -- QOI_OP_RGB
      match rest with
      | r :: g :: b :: rest => some ({ prev with r, g, b }, 0, rest)
      | _ => none
    else if tag = 0xFF then                              -- QOI_OP_RGBA
      match rest with
      | r :: g :: b :: a :: rest => some ({ r, g, b, a }, 0, rest)
      | _ => none
    else if tag >>> 6 = 0 then                           -- QOI_OP_INDEX
      some (index[tag.toNat % 64]'(Nat.mod_lt _ (by decide)), 0, rest)
    else if tag >>> 6 = 1 then                           -- QOI_OP_DIFF: three 2-bit deltas, bias 2
      some ({ prev with r := prev.r + (tag >>> 4 &&& 3) - 2
                        g := prev.g + (tag >>> 2 &&& 3) - 2
                        b := prev.b + (tag &&& 3) - 2 }, 0, rest)
    else if tag >>> 6 = 2 then                           -- QOI_OP_LUMA: green delta, then r/b relative to it
      match rest with
      | next :: rest =>
        let dg : UInt8 := (tag &&& 63) - 32
        some ({ prev with r := prev.r + dg + (next >>> 4) - 8
                          g := prev.g + dg
                          b := prev.b + dg + (next &&& 15) - 8 }, 0, rest)
      | [] => none
    else                                                 -- QOI_OP_RUN: bias 1
      some (prev, (tag &&& 63).toNat, rest)

/-- Decode `n` pixels from the chunk stream. -/
def pixels (n : Nat) (index : Vector Pixel 64) (prev : Pixel) (bytes : List UInt8) :
    Option (List Pixel) :=
  match n with
  | 0 => some []
  | n + 1 => do
    let (px, extra, rest) ← chunk index prev bytes
    let extra := min extra n
    let more ← pixels (n - extra) (index.set px.hash px) px rest
    return List.replicate (extra + 1) px ++ more

/-- A big-endian 32-bit number. -/
def be32 (a b c d : UInt8) : Nat :=
  a.toNat * 2 ^ 24 + b.toNat * 2 ^ 16 + c.toNat * 2 ^ 8 + d.toNat

def maxPixels : Nat := 400000000

structure Image where
  width : Nat
  height : Nat
  channels : UInt8
  colorspace : UInt8
  pixels : List Pixel
  deriving DecidableEq, Repr

def decode : List UInt8 → Option Image
  | 0x71 :: 0x6F :: 0x69 :: 0x66 :: w₀ :: w₁ :: w₂ :: w₃ :: h₀ :: h₁ :: h₂ :: h₃ :: channels :: colorspace
      :: body => do
    let width := be32 w₀ w₁ w₂ w₃
    let height := be32 h₀ h₁ h₂ h₃
    guard (channels = 3 ∨ channels = 4)
    guard (colorspace ≤ 1)
    guard (width * height ≤ maxPixels)
    guard (body.length ≥ 8)
    let chunks := body.take (body.length - 8)
    let px ← pixels (width * height) (Vector.replicate 64 ⟨0, 0, 0, 0⟩) ⟨0, 0, 0, 255⟩ chunks
    return { width, height, channels, colorspace, pixels := px }
  | _ => none

/-- The decoded pixels as the flat RGBA byte string every decoder in this repo outputs. -/
def Image.rgba (img : Image) : List UInt8 :=
  img.pixels.flatMap fun p => [p.r, p.g, p.b, p.a]

end QOI.Spec

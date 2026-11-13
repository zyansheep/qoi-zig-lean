import QOI.Spec
import QOI.Cli

/-- The executable specification: slow, list-based, and the fuzzing oracle for every other decoder. -/
def specRGBA (b : ByteArray) : Option ByteArray :=
  (QOI.Spec.decode b.toList).map fun img => ⟨img.rgba.toArray⟩

def main (args : List String) : IO UInt32 := QOI.Cli.run specRGBA args

import QOI.Fast.Impl
import QOI.Fast.Proof

/-!
# The optimised QOI decoder, proven equal to the specification

* `QOI/Fast/Impl.lean` — the implementation (`decodeRGBA`, `loop`), plain Lean over `ByteArray`/`USize`.
* `QOI/Fast/Proof.lean` — the proof that it computes `QOI.Spec.decode`, for every input
  (accepted and rejected ones alike).
-/

namespace QOI.Fast

/-- The fast decoder returns exactly the spec's RGBA bytes, and rejects exactly what the spec rejects. -/
theorem decodeRGBA_eq_spec (b : ByteArray) :
    decodeRGBA b = (QOI.Spec.decode b.toList).map (fun img => ⟨img.rgba.toArray⟩) :=
  decodeRGBA_eq_spec' b

end QOI.Fast

#print axioms QOI.Fast.decodeRGBA_eq_spec

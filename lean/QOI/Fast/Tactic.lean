/-! Tactics shared by the implementation (bounds proofs) and the correctness proof. -/

namespace QOI.Fast

/-- Arithmetic on `USize` whose results do not wrap: case on the platform word size and use `omega`.
(`clear_value *` first: `simp at *` cannot rewrite a hypothesis that a `let` value depends on.) -/
macro "usize_arith" : tactic => `(tactic| (
  (try clear_value *)
  rcases System.Platform.numBits_eq with hnb | hnb <;>
  simp only [USize.toNat_add, USize.toNat_sub, USize.toNat_mul, USize.toNat_div, USize.toNat_ofNat,
    USize.lt_iff_toNat_lt, USize.le_iff_toNat_le, ← USize.toNat_inj, USize.size_eq_two_pow,
    UInt8.toNat_toUSize, Nat.toUSize_eq, USize.toNat_ofNat', hnb, Nat.reducePow, Nat.reduceMod, ne_eq] at * <;> omega))

end QOI.Fast

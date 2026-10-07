-- Copyright (c) 2026 Scott Armstrong and Amélie Loher. All rights reserved.
-- Released under Apache 2.0 license as described in the file LICENSE.
module
public import RothschildStein.G3.QuasiExponentialLog
public import RothschildStein.G3.FiniteWords
@[expose] public section
set_option autoImplicit false
set_option relaxedAutoImplicit false
namespace RothschildStein.G3

/-- Positive weights give one factor-count budget for every retained word. -/
theorem weighted_commutatorSchedule_length_le {a s : ℕ} (p : Fin a → ℕ+)
    (I : List (Fin a)) (hI : I ≠ []) (hweight : wordWeight p I ≤ s) :
    (G1.commutatorSchedule I).length ≤ 3*2^s := by
  rw [quasiExponential_primitive_count I hI]
  apply (Nat.sub_le _ _).trans
  exact Nat.mul_le_mul_left 3 (Nat.pow_le_pow_right (by decide)
    ((Nat.sub_le I.length 1).trans ((length_le_weight p I).trans hweight)))
end RothschildStein.G3

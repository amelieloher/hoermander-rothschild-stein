-- Copyright (c) 2026 Scott Armstrong and Amélie Loher. All rights reserved.
-- Released under Apache 2.0 license as described in the file LICENSE.
module

public import RothschildStein.H3.SecondJetHolderConstant
public import Mathlib.Topology.Instances.ENNReal.Lemmas

set_option autoImplicit false
set_option relaxedAutoImplicit false
@[expose] public section
noncomputable section
namespace RothschildStein.H3
open scoped ENNReal

/-- A positive real constant for the complete weight-two
family with drift coefficient one, fixed before the input function. -/
def weightTwoHolderConstant {q : ℕ} (B c : Fin q → Fin q → ℝ) : ℝ :=
  ((q : ℝ)^2 + (1 + (q : ℝ))) * secondJetHolderMax B c

/-- The real family constant is positive, including q = 0. -/
theorem weightTwoHolderConstant_pos {q : ℕ} (B c : Fin q → Fin q → ℝ) :
    0 < weightTwoHolderConstant B c := by
  have hL : 0 < secondJetHolderMax B c := lt_of_lt_of_le zero_lt_one (one_le_secondJetHolderMax B c)
  unfold weightTwoHolderConstant
  positivity

/-- Conversion to the literal fixed ENNReal coefficient
adds no comparison factor. -/
theorem ofReal_weightTwoHolderConstant {q : ℕ} (B c : Fin q → Fin q → ℝ) :
    ENNReal.ofReal (weightTwoHolderConstant B c) =
      ((q : ℝ≥0∞)^2 + (1 + (q : ℝ≥0∞))) * ENNReal.ofReal (secondJetHolderMax B c) := by
  unfold weightTwoHolderConstant
  rw [ENNReal.ofReal_mul (by positivity), ENNReal.ofReal_add (by positivity) (by positivity),
    ENNReal.ofReal_add zero_le_one (Nat.cast_nonneg q)]
  simp only [ENNReal.ofReal_pow (Nat.cast_nonneg q), ENNReal.ofReal_natCast, ENNReal.ofReal_one]

end RothschildStein.H3

-- Copyright (c) 2026 Scott Armstrong and Amélie Loher. All rights reserved.
-- Released under Apache 2.0 license as described in the file LICENSE.
module

public import Mathlib.Analysis.SpecialFunctions.Integrals.Basic

@[expose] public section
set_option autoImplicit false
set_option relaxedAutoImplicit false
noncomputable section
open MeasureTheory
open scoped BigOperators

namespace RothschildStein.G4

/-- Integrating the signed bracket polynomial produces exactly the
(k+1)! normalization in the coefficient derivative expansion
(BB Lemma 9.48, pp. 441–442). -/
theorem integral_signed_bracket_polynomial {E : Type*} [NormedAddCommGroup E]
    [NormedSpace ℝ E] [CompleteSpace E] (V : ℕ → E) (n : ℕ) :
    (∫ s in (0 : ℝ)..1, ∑ k ∈ Finset.range (n + 1),
      ((-1 : ℝ) ^ k * s ^ k / (k.factorial : ℝ)) • V k) =
      ∑ k ∈ Finset.range (n + 1), ((-1 : ℝ) ^ k / ((k + 1).factorial : ℝ)) • V k := by
  have hi : ∀ k ∈ Finset.range (n + 1), IntervalIntegrable
      (fun s : ℝ => ((-1 : ℝ) ^ k * s ^ k / (k.factorial : ℝ)) • V k) volume 0 1 := by
    intro k _
    exact (((continuous_const.mul (continuous_id.pow k)).div_const _).smul
      continuous_const).intervalIntegrable _ _
  rw [intervalIntegral.integral_finsetSum hi]
  apply Finset.sum_congr rfl
  intro k _
  rw [intervalIntegral.integral_smul_const, intervalIntegral.integral_div,
    intervalIntegral.integral_const_mul, integral_pow]
  congr 1
  simp only [one_pow, zero_pow (Nat.succ_ne_zero k), sub_zero, Nat.factorial_succ,
    Nat.cast_mul, Nat.cast_add, Nat.cast_one]
  field_simp

end RothschildStein.G4

-- Copyright (c) 2026 Scott Armstrong and Amélie Loher. All rights reserved.
-- Released under Apache 2.0 license as described in the file LICENSE.
module

public import HeatKernel.Moser.CaccioppoliBilinearAbsorption
public import HeatKernel.Moser.MeanValuePowerFluxCoercivity
import Mathlib.Tactic

/-! # Half-power coercivity after coefficient-form absorption -/

@[expose] public section
set_option autoImplicit false
set_option relaxedAutoImplicit false
namespace HeatKernel

/-- Half of the principal coefficient energy controls the half-power gradient
with the reciprocal exponent coefficient, for every positive bilinear form. -/
theorem linearTail_half_power_bilinear_coercivity
    {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    (B : E →L[ℝ] E →L[ℝ] ℝ) (hpos : ∀ v, 0 ≤ B v v)
    {M p s : ℝ} (hM : 0 < M) (hp : 2 ≤ p) (η : ℝ) (g : E) :
    (1 / p) * linearTailPositivePowerSlope M (p / 2) s ^ 2 * η ^ 2 * B g g ≤
      linearTailPositivePowerSlope M (p - 1) s / 2 * η ^ 2 * B g g := by
  have h := mul_le_mul_of_nonneg_right
    (linearTailPositivePowerSlope_half_sq_le_linear (s := s) hM hp)
    (mul_nonneg (sq_nonneg η) (hpos g))
  have hscaled := mul_le_mul_of_nonneg_left h
    (show 0 ≤ 1 / p by positivity)
  convert hscaled using 1 <;> field_simp

/-- The absorbed matrix flux controls the half-power energy in both truncation
regions. The low-region power error and high-region quadratic tail are retained
literally, with no finiteness or limiting hypothesis. -/
theorem linearTail_half_power_bilinear_absorption
    {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    (B : E →L[ℝ] E →L[ℝ] ℝ) (hsym : ∀ v w, B v w = B w v)
    (hpos : ∀ v, 0 ≤ B v v) {M p s : ℝ}
    (hM : 0 < M) (hp : 2 ≤ p) (hs : 0 ≤ s) (η : ℝ) (g d : E) :
    (1 / p) * linearTailPositivePowerSlope M (p / 2) s ^ 2 * η ^ 2 * B g g -
      (if s < M then (2 / (p - 1)) * s ^ p else
        2 * (s ^ 2 * M ^ (p - 2))) * B d d ≤
      linearTailPositivePowerSlope M (p - 1) s * η ^ 2 * B g g +
        2 * (linearTailPowerWeakSolutionTest hM (show 1 ≤ p - 1 by linarith)).toFun s *
          η * B g d := by
  have hco := linearTail_half_power_bilinear_coercivity B hpos (s := s) hM hp η g
  rcases eq_or_lt_of_le hs with hz | hspos
  · subst s
    simp only [linearTailPositivePowerSlope, lt_self_iff_false, ↓reduceIte,
      WeakSolutionScalarTest.map_zero, Real.zero_rpow (by linarith : p ≠ 0)]
    simp
  · by_cases hl : s < M
    · rw [ite_eq_left hl]
      exact (sub_le_sub_right hco _).trans
        (caccioppoli_bilinear_power_below B hsym hpos hM hp hspos hl η g d)
    · rw [ite_eq_right hl]
      exact (sub_le_sub_right hco _).trans
        (caccioppoli_bilinear_power_above B hsym hpos hM hp (le_of_not_gt hl) η g d)

end HeatKernel

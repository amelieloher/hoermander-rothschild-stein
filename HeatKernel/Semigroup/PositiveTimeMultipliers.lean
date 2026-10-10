-- Copyright (c) 2026 Scott Armstrong and Amélie Loher. All rights reserved.
-- Released under Apache 2.0 license as described in the file LICENSE.
module

public import HeatKernel.Semigroup.ScalarMultipliers

/-! # Resolvent factors for positive-time heat multipliers

Polynomial decay against the smooth exponential glue makes division by the resolvent
coordinate continuous at zero. This supplies the factor placing heat vectors in the
operator domain.
-/

@[expose] public section
noncomputable section
namespace HeatKernel

/-- The continuous factor of the heat multiplier through the resolvent coordinate. -/
def heatResolventFactor (t r : ℝ) : ℝ := r⁻¹ * heatMultiplier t r

theorem heatResolventFactor_eq (t r : ℝ) :
    heatResolventFactor t r = (Real.exp t / t) *
      ((Polynomial.X : Polynomial ℝ).eval (r / t)⁻¹ * expNegInvGlue (r / t)) := by
  by_cases ht : t = 0
  · simp [heatResolventFactor, heatMultiplier, ht]
  by_cases hr : r = 0
  · simp [heatResolventFactor, hr]
  simp only [heatResolventFactor, heatMultiplier, Polynomial.eval_X, inv_div]
  field_simp [ht, hr]

theorem continuous_heatResolventFactor (t : ℝ) : Continuous (heatResolventFactor t) := by
  have heq : heatResolventFactor t = fun r => (Real.exp t / t) *
      ((Polynomial.X : Polynomial ℝ).eval (r / t)⁻¹ * expNegInvGlue (r / t)) := by
    funext r
    exact heatResolventFactor_eq t r
  rw [heq]
  exact continuous_const.mul
    ((expNegInvGlue.continuous_polynomial_eval_inv_mul Polynomial.X).comp
      (continuous_id.div_const t))

@[simp] theorem mul_heatResolventFactor (t r : ℝ) :
    r * heatResolventFactor t r = heatMultiplier t r := by
  by_cases hr : r = 0
  · simp [hr]
  rw [heatResolventFactor, ← mul_assoc, mul_inv_cancel₀ hr, one_mul]

/-- The multiplier of the form operator applied after heat evolution. -/
def heatGeneratorMultiplier (t r : ℝ) : ℝ := (1 - r) * heatResolventFactor t r

theorem continuous_heatGeneratorMultiplier (t : ℝ) : Continuous (heatGeneratorMultiplier t) :=
  (continuous_const.sub continuous_id).mul (continuous_heatResolventFactor t)

theorem mul_heatMultiplier_add_generatorMultiplier (t r : ℝ) :
    r * (heatMultiplier t r + heatGeneratorMultiplier t r) = heatMultiplier t r := by
  calc
    _ = r * heatResolventFactor t r := by
      rw [← mul_heatResolventFactor t r]
      unfold heatGeneratorMultiplier
      ring
    _ = _ := mul_heatResolventFactor t r

end HeatKernel

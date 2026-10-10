-- Copyright (c) 2026 Scott Armstrong and Amélie Loher. All rights reserved.
-- Released under Apache 2.0 license as described in the file LICENSE.
module

public import HeatKernel.Semigroup.PositiveTimeMultipliers
public import HeatKernel.Semigroup.BoundedHeatOperators

/-! # Resolvent-range factorization of heat operators

Continuous functional calculus factors the heat operator through the resolvent and
identifies the bounded operator representing its generator value.
-/

@[expose] public section
noncomputable section
open Set
namespace HeatKernel
variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℂ E] [CompleteSpace E]

/-- The bounded multiplier representing the generator after positive-time evolution. -/
def heatGeneratorOperator (R : E →L[ℂ] E) (t : ℝ) : E →L[ℂ] E :=
  cfc (heatGeneratorMultiplier t) R

theorem heat_cfc_generator_resolvent_equation (R : E →L[ℂ] E)
    (hR : IsSelfAdjoint R) (t : ℝ) :
    R * ((cfc (heatMultiplier t) R : E →L[ℂ] E) + heatGeneratorOperator R t) =
      cfc (heatMultiplier t) R := by
  have hsum : ContinuousOn (fun r => heatMultiplier t r + heatGeneratorMultiplier t r)
      (spectrum ℝ R) :=
    ((continuous_heatMultiplier t).add (continuous_heatGeneratorMultiplier t)).continuousOn
  have hc := cfc_mul (fun r : ℝ => r)
    (fun r => heatMultiplier t r + heatGeneratorMultiplier t r) R continuous_id.continuousOn hsum
  have hf : (fun r : ℝ => r * (heatMultiplier t r + heatGeneratorMultiplier t r)) =
      heatMultiplier t := by
    funext r
    exact mul_heatMultiplier_add_generatorMultiplier t r
  rw [hf, cfc_id' ℝ R hR, cfc_add R (heatMultiplier t) (heatGeneratorMultiplier t)
    (continuous_heatMultiplier t).continuousOn (continuous_heatGeneratorMultiplier t).continuousOn] at hc
  exact hc.symm

theorem heat_cfc_generator_resolvent_equation_apply (R : E →L[ℂ] E)
    (hR : IsSelfAdjoint R) (t : ℝ) (x : E) :
    R ((cfc (heatMultiplier t) R : E →L[ℂ] E) x + heatGeneratorOperator R t x) =
      (cfc (heatMultiplier t) R : E →L[ℂ] E) x := by
  simpa only [mul_apply_eq_comp, add_apply] using
    congrArg (fun T : E →L[ℂ] E => T x) (heat_cfc_generator_resolvent_equation R hR t)

end HeatKernel

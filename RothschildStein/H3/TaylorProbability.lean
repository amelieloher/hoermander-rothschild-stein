-- Copyright (c) 2026 Scott Armstrong and Amélie Loher. All rights reserved.
-- Released under Apache 2.0 license as described in the file LICENSE.
module

public import RothschildStein.H3.IntegralPowerBound
public import Mathlib.MeasureTheory.Measure.WithDensity
public import Mathlib.Analysis.SpecialFunctions.Integrals.Basic

set_option autoImplicit false
set_option relaxedAutoImplicit false
set_option backward.isDefEq.respectTransparency false
@[expose] public section
noncomputable section
namespace RothschildStein.H3
open Set MeasureTheory

/-- The normalized Taylor remainder weight on the unit interval. -/
def taylorProbability : Measure ℝ :=
  (volume.restrict (Ioc (0 : ℝ) 1)).withDensity (fun t => ENNReal.ofReal (2 * (1 - t)))

/-- The normalized Taylor weight has total mass exactly one. -/
theorem taylorProbability_isProbability : IsProbabilityMeasure taylorProbability := by
  apply isProbabilityMeasure_iff.mpr
  have hi : Integrable (fun t : ℝ => 2 * (1 - t)) (volume.restrict (Ioc (0 : ℝ) 1)) :=
    ((continuous_const.mul (continuous_const.sub continuous_id)).intervalIntegrable 0 1).1
  have hn : 0 ≤ᵐ[volume.restrict (Ioc (0 : ℝ) 1)] (fun t : ℝ => 2 * (1 - t)) := by
    filter_upwards [ae_restrict_mem measurableSet_Ioc] with t ht
    exact mul_nonneg (by norm_num) (sub_nonneg.mpr ht.2)
  have hc : (∫ t in (0 : ℝ)..1, 2 * (1 - t)) = 1 := by
    rw [intervalIntegral.integral_const_mul,
      intervalIntegral.integral_sub (f := fun _ : ℝ => (1 : ℝ)) (g := fun t : ℝ => t)
        intervalIntegrable_const (continuous_id.intervalIntegrable 0 1)]
    norm_num [integral_id]
  change ((volume.restrict (Ioc (0 : ℝ) 1)).withDensity
    (fun t => ENNReal.ofReal (2 * (1 - t)))) univ = 1
  rw [withDensity_apply _ MeasurableSet.univ, setLIntegral_univ,
    ← ofReal_integral_eq_lintegral_ofReal hi hn,
    ← intervalIntegral.integral_of_le (by norm_num : (0 : ℝ) ≤ 1), hc]
  norm_num

end RothschildStein.H3

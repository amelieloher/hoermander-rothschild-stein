-- Copyright (c) 2026 Scott Armstrong and Amélie Loher. All rights reserved.
-- Released under Apache 2.0 license as described in the file LICENSE.
module

public import RothschildStein.H3.TaylorProbability
public import Mathlib.MeasureTheory.Integral.Bochner.ContinuousLinearMap

set_option autoImplicit false
set_option relaxedAutoImplicit false
set_option backward.isDefEq.respectTransparency false
@[expose] public section
noncomputable section
namespace RothschildStein.H3
open Set MeasureTheory

/-- The normalized probability integral is twice the actual
unit-step Taylor remainder integral, for every real integrand. -/
theorem integral_taylorProbability (h : ℝ → ℝ) :
    (∫ t, h t ∂taylorProbability) =
      2 * ∫ t in (0 : ℝ)..1, (1 - t) * h t := by
  unfold taylorProbability
  have hd : Measurable (fun t : ℝ => ENNReal.ofReal (2 * (1 - t))) :=
    (continuous_const.mul (continuous_const.sub continuous_id)).measurable.ennreal_ofReal
  rw [integral_withDensity_eq_integral_toReal_smul hd
    (Filter.Eventually.of_forall fun _ => ENNReal.ofReal_lt_top) h]
  have he : (fun t : ℝ => (ENNReal.ofReal (2 * (1 - t))).toReal • h t)
      =ᵐ[volume.restrict (Ioc (0 : ℝ) 1)] (fun t => 2 * ((1 - t) * h t)) := by
    filter_upwards [ae_restrict_mem measurableSet_Ioc] with t ht
    rw [ENNReal.toReal_ofReal (mul_nonneg (by norm_num) (sub_nonneg.mpr ht.2)), smul_eq_mul]
    ring
  rw [integral_congr_ae he, integral_const_mul,
    ← intervalIntegral.integral_of_le (by norm_num : (0 : ℝ) ≤ 1)]

end RothschildStein.H3

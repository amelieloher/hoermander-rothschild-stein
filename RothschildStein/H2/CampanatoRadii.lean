-- Copyright (c) 2026 Scott Armstrong and Amélie Loher. All rights reserved.
-- Released under Apache 2.0 license as described in the file LICENSE.
module
public import RothschildStein.H2.CampanatoConstants
public import RothschildStein.H2.VolumeGrowth
@[expose] public section
set_option autoImplicit false
set_option relaxedAutoImplicit false
noncomputable section
open Set MeasureTheory Metric
open scoped ENNReal
namespace RothschildStein.H2
variable {X : Type*} [MetricSpace X] [MeasurableSpace X] [BorelSpace X]

/-- Comparing minimisers at two nested radii (BB Lemma 7.42).
The ratio is fixed when the radii are both scaled dyadically. -/
theorem campanatoConstant_radii (P : DoublingPatch X) {α : ℝ}
    {u : X → ℝ} (hu : MemCampanato α P u) {x : X} (hx : x ∈ P.S)
    {r s : ℝ} (hr : 0 < r) (hrs : r ≤ s) (hsρ : s ≤ 6 * P.ρ) :
    |campanatoConstant P u x r - campanatoConstant P u x s| ≤
      (campanatoSeminorm α P u).toReal *
        (r ^ α + s ^ α * (P.C_D * (s / r) ^ Real.logb 2 P.C_D)) := by
  have hs : 0 < s := hr.trans_le hrs
  have hv := P.doubling x hx s hs hsρ
  have hvr := P.doubling x hx r hr (hrs.trans hsρ)
  have hm : 0 < (P.μ (ball x r)).toReal := ENNReal.toReal_pos hvr.1.ne' hvr.2.1.ne
  have hCn : 0 ≤ P.C_D * (s / r) ^ Real.logb 2 P.C_D :=
    mul_nonneg (by linarith [P.one_lt_C_D]) (Real.rpow_nonneg (div_nonneg hs.le hr.le) _)
  have hg := P.compare_rpow hx hr hrs hsρ
  have hvol := ENNReal.toReal_mono
    (ENNReal.mul_ne_top ENNReal.ofReal_ne_top hvr.2.1.ne) hg
  rw [ENNReal.toReal_mul, ENNReal.toReal_ofReal hCn] at hvol
  have hcmp := oscillation_constants_comparison (ball_subset_ball hrs) hv.2.1
    (hu.1.mono_set ((ball_subset_ball hsρ).trans (P.incl x hx)))
    (campanatoConstant P u x r) (campanatoConstant P u x s)
  have hbr := campanatoConstant_integral_bound P hu hx hr (hrs.trans hsρ)
  have hbs := campanatoConstant_integral_bound P hu hx hs hsρ
  have hvb := mul_le_mul_of_nonneg_left hvol
    (mul_nonneg (ENNReal.toReal_nonneg (a := campanatoSeminorm α P u)) (Real.rpow_nonneg hs.le α))
  nlinarith
end RothschildStein.H2

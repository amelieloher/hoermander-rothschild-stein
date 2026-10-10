-- Copyright (c) 2026 Scott Armstrong and Amélie Loher. All rights reserved.
-- Released under Apache 2.0 license as described in the file LICENSE.
module

public import Mathlib.Analysis.SpecialFunctions.Log.Deriv
public import Mathlib.Analysis.Calculus.MeanValue
import Mathlib.Tactic

/-! # A globally Lipschitz lower truncation of the logarithm -/

@[expose] public section
set_option autoImplicit false
set_option relaxedAutoImplicit false
noncomputable section
open Set Filter
open scoped Topology NNReal
namespace HeatKernel.Sobolev

/-- The logarithm held constant below a positive threshold. -/
def lowerTruncatedLog (c s : ℝ) : ℝ := Real.log (max c s)

/-- A chain-rule factor for the lower-truncated logarithm, including its threshold. -/
def lowerTruncatedLogSlope (c s : ℝ) : ℝ := if s < c then 0 else s⁻¹

/-- The lower-truncated logarithm has Lipschitz constant equal to the reciprocal threshold. -/
theorem lipschitzWith_lowerTruncatedLog {c : ℝ} (hc : 0 < c) :
    LipschitzWith ⟨c⁻¹, (inv_pos.mpr hc).le⟩ (lowerTruncatedLog c) := by
  have hlog : LipschitzOnWith ⟨c⁻¹, (inv_pos.mpr hc).le⟩ Real.log (Ici c) := by
    apply Convex.lipschitzOnWith_of_nnnorm_deriv_le
      (fun x hx => Real.differentiableAt_log (hc.trans_le hx).ne') _ (convex_Ici c)
    intro x hx
    change ‖deriv Real.log x‖ ≤ c⁻¹
    rw [Real.deriv_log, Real.norm_eq_abs, abs_of_pos (inv_pos.mpr (hc.trans_le hx))]
    simpa only [one_div] using one_div_le_one_div_of_le hc hx
  have hmax : LipschitzWith 1 (fun s : ℝ => max c s) := LipschitzWith.id.const_max c
  apply LipschitzWith.of_dist_le_mul
  intro x y
  exact (hlog.dist_le_mul _ (le_max_left _ _) _ (le_max_left _ _)).trans
    (mul_le_mul_of_nonneg_left (by simpa only [NNReal.coe_one, one_mul] using hmax.dist_le_mul x y)
      (inv_nonneg.mpr hc.le))

/-- Away from the threshold, the truncated logarithm is C¹. -/
theorem contDiffAt_lowerTruncatedLog {c s : ℝ} (hc : 0 < c) (hs : s ≠ c) :
    ContDiffAt ℝ 1 (lowerTruncatedLog c) s := by
  rcases lt_or_gt_of_ne hs with hsc | hcs
  · apply (contDiffAt_const (c := Real.log c)).congr_of_eventuallyEq
    filter_upwards [Iio_mem_nhds hsc] with t ht
    simp only [lowerTruncatedLog, max_eq_left ht.le]
  · apply (Real.contDiffAt_log.mpr (hc.trans hcs).ne').congr_of_eventuallyEq
    filter_upwards [Ioi_mem_nhds hcs] with t ht
    simp only [lowerTruncatedLog, max_eq_right ht.le]

/-- The displayed factor agrees with the derivative away from the threshold. -/
theorem lowerTruncatedLogSlope_eq_deriv {c s : ℝ} (hc : 0 < c) (hs : s ≠ c) :
    lowerTruncatedLogSlope c s = deriv (lowerTruncatedLog c) s := by
  rcases lt_or_gt_of_ne hs with hsc | hcs
  · have hder : HasDerivAt (lowerTruncatedLog c) 0 s := by
      apply (hasDerivAt_const s (Real.log c)).congr_of_eventuallyEq
      filter_upwards [Iio_mem_nhds hsc] with t ht
      simp only [lowerTruncatedLog, max_eq_left ht.le]
    simpa only [lowerTruncatedLogSlope, ite_eq_left hsc] using hder.deriv.symm
  · have hder : HasDerivAt (lowerTruncatedLog c) s⁻¹ s := by
      apply (Real.hasDerivAt_log (hc.trans hcs).ne').congr_of_eventuallyEq
      filter_upwards [Ioi_mem_nhds hcs] with t ht
      simp only [lowerTruncatedLog, max_eq_right ht.le]
    simpa only [lowerTruncatedLogSlope, ite_eq_right (not_lt.mpr hcs.le)] using hder.deriv.symm

end HeatKernel.Sobolev

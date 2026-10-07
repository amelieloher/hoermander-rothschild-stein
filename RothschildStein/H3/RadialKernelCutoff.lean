-- Copyright (c) 2026 Scott Armstrong and Amélie Loher. All rights reserved.
-- Released under Apache 2.0 license as described in the file LICENSE.
module

public import Mathlib.Topology.MetricSpace.Lipschitz
public import Mathlib.Tactic

set_option autoImplicit false
set_option relaxedAutoImplicit false
@[expose] public section
noncomputable section
namespace RothschildStein.H3

/-- The piecewise linear radial profile from BB p. 350,
equal to one through radius 2r and zero from radius 3r. -/
def radialKernelCutoffProfile (r s : ℝ) : ℝ := min 1 (max 0 (3 - s / r))

/-- The cutoff has values in the unit interval. -/
theorem radialKernelCutoffProfile_range (r s : ℝ) :
    0 ≤ radialKernelCutoffProfile r s ∧ radialKernelCutoffProfile r s ≤ 1 :=
  ⟨le_min (by norm_num) (le_max_left _ _), min_le_left _ _⟩

/-- The profile is exactly one on the inner plateau. -/
theorem radialKernelCutoffProfile_eq_one {r s : ℝ} (hr : 0 < r) (hs : s ≤ 2 * r) :
    radialKernelCutoffProfile r s = 1 := by
  have hsr : s / r ≤ 2 := (div_le_iff₀ hr).mpr (by linarith)
  unfold radialKernelCutoffProfile
  apply min_eq_left
  exact (by linarith : (1 : ℝ) ≤ 3 - s / r).trans (le_max_right _ _)

/-- The profile vanishes at and beyond the outer radius. -/
theorem radialKernelCutoffProfile_eq_zero {r s : ℝ} (hr : 0 < r) (hs : 3 * r ≤ s) :
    radialKernelCutoffProfile r s = 0 := by
  have hsr : 3 ≤ s / r := (le_div_iff₀ hr).mpr (by linarith)
  unfold radialKernelCutoffProfile
  rw [max_eq_left (by linarith : 3 - s / r ≤ 0)]
  norm_num

/-- The precise cutoff Lipschitz constant is the reciprocal
of r, with no smoothness assertion for the piecewise linear profile. -/
theorem radialKernelCutoffProfile_sub_le {r : ℝ} (hr : 0 < r) (s t : ℝ) :
    |radialKernelCutoffProfile r s - radialKernelCutoffProfile r t| ≤ |s - t| / r := by
  have hmax := abs_max_sub_max_le_max (0 : ℝ) (3 - s / r) 0 (3 - t / r)
  have hmin := abs_min_sub_min_le_max (1 : ℝ) (max 0 (3 - s / r))
    1 (max 0 (3 - t / r))
  simp only [sub_self, abs_zero] at hmax hmin
  rw [max_eq_right (show (0 : ℝ) ≤ |(3 - s / r) - (3 - t / r)| from abs_nonneg _)] at hmax
  rw [max_eq_right (show (0 : ℝ) ≤ |max 0 (3 - s / r) - max 0 (3 - t / r)|
    from abs_nonneg _)] at hmin
  have he : |(3 - s / r) - (3 - t / r)| = |s - t| / r := by
    rw [show (3 - s / r) - (3 - t / r) = -(s - t) / r by ring,
      abs_div, abs_neg, abs_of_pos hr]
  exact hmin.trans (hmax.trans_eq he)

/-- The actual radial profile is continuous. -/
theorem radialKernelCutoffProfile_continuous (r : ℝ) :
    Continuous (radialKernelCutoffProfile r) :=
  continuous_const.min (continuous_const.max
    (continuous_const.sub (continuous_id.div_const r)))

end RothschildStein.H3

-- Copyright (c) 2026 Scott Armstrong and Amélie Loher. All rights reserved.
-- Released under Apache 2.0 license as described in the file LICENSE.
module

public import HeatKernel.Poincare.ComparableVolumeConstants
public import HeatKernel.Poincare.BallVolumeComparability
public import HeatKernel.Poincare.WhitneyAveragingContainment

/-! Comparing constants on neighboring Whitney averaging balls. -/

@[expose] public section
set_option autoImplicit false
set_option relaxedAutoImplicit false
noncomputable section
open Set Metric MeasureTheory
open scoped ENNReal

namespace HeatKernel

/-- Neighboring Whitney averaging constants differ by at most the homogeneous volume
comparison factor times the sum of their normalized oscillation costs. -/
theorem ofReal_abs_sub_le_of_neighboring_ball_eLpNorm_bounds {E : Type*} [MetricSpace E]
    [MeasurableSpace E] (μ : Measure E) (Q : ℕ) (v : ℝ≥0∞) (hv0 : v ≠ 0) (hvtop : v ≠ ⊤)
    (hvolume : ∀ x : E, ∀ r : ℝ, 0 < r → μ (ball x r) = ENNReal.ofReal (r ^ Q) * v)
    (u : E → ℝ) (c d : ℝ) (z w : E) {a b : ℝ} (ha : 0 < a) (hb : 0 < b)
    (hab : a ≤ 2 * b) (hba : b ≤ 2 * a)
    (hmeet : (ball z (5 * a) ∩ ball w (5 * b)).Nonempty)
    {p : ℝ≥0∞} (hp : 1 ≤ p) (hptop : p ≠ ⊤) (e₁ e₂ : ℝ≥0∞)
    (hfirst : eLpNorm (fun x => u x - c) p (μ.restrict (ball z (20 * a))) ≤
      e₁ * μ (ball z a) ^ (1 / p.toReal))
    (hsecond : eLpNorm (fun x => u x - d) p (μ.restrict (ball w (20 * b))) ≤
      e₂ * μ (ball w b) ^ (1 / p.toReal)) :
    ENNReal.ofReal |c - d| ≤ ((2 : ℝ≥0∞) ^ Q) ^ (1 / p.toReal) * (e₁ + e₂) := by
  have hA0 : μ (ball z a) ≠ 0 := by
    rw [hvolume z a ha]
    exact mul_ne_zero (ENNReal.ofReal_pos.mpr (pow_pos ha Q)).ne' hv0
  have hAtop : μ (ball z a) ≠ ⊤ := by
    rw [hvolume z a ha]
    exact ENNReal.mul_ne_top ENNReal.ofReal_ne_top hvtop
  have hAU : ball z a ⊆ ball z (20 * a) := ball_subset_ball (by linarith)
  have hAV := ball_subset_twenty_dilate_of_five_dilates_intersect hab hmeet
  have hv := measure_ball_le_two_pow_mul_of_radius_le_two_mul μ Q v hvolume z w ha hb hba
  have hh := ofReal_abs_sub_le_of_comparable_volume_eLpNorm_bounds μ u c d hAU hAV
    hA0 hAtop hp hptop e₁ e₂ (μ (ball w b)) ((2 : ℝ≥0∞) ^ Q) hv hfirst hsecond
  have hD : (1 : ℝ≥0∞) ≤ 2 ^ Q := one_le_pow₀ (by norm_num)
  have hr : 0 ≤ 1 / p.toReal := one_div_nonneg.mpr ENNReal.toReal_nonneg
  have hDroot : (1 : ℝ≥0∞) ≤ ((2 : ℝ≥0∞) ^ Q) ^ (1 / p.toReal) := by
    simpa only [ENNReal.one_rpow] using ENNReal.rpow_le_rpow hD hr
  calc
    ENNReal.ofReal |c - d| ≤ e₁ + e₂ * ((2 : ℝ≥0∞) ^ Q) ^ (1 / p.toReal) := hh
    _ ≤ e₁ * ((2 : ℝ≥0∞) ^ Q) ^ (1 / p.toReal) +
        e₂ * ((2 : ℝ≥0∞) ^ Q) ^ (1 / p.toReal) := by
      apply add_le_add _ le_rfl
      simpa only [mul_one] using mul_le_mul_right hDroot e₁
    _ = ((2 : ℝ≥0∞) ^ Q) ^ (1 / p.toReal) * (e₁ + e₂) := by rw [mul_add]; ac_rfl

end HeatKernel

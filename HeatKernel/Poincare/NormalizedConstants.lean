-- Copyright (c) 2026 Scott Armstrong and Amélie Loher. All rights reserved.
-- Released under Apache 2.0 license as described in the file LICENSE.
module

public import HeatKernel.Poincare.OverlappingConstants

/-! Removing the common volume factor from neighboring averaging constants. -/

@[expose] public section
set_option autoImplicit false
set_option relaxedAutoImplicit false
noncomputable section
open Set MeasureTheory
open scoped ENNReal

namespace HeatKernel

/-- Oscillation estimates expressed in units of the common subset's volume control the
difference of their constants, with exactly the sum of their normalized costs. -/
theorem ofReal_abs_sub_le_of_common_volume_eLpNorm_bounds {E : Type*} [MeasurableSpace E]
    (μ : Measure E) (f : E → ℝ) (c d : ℝ) {A U V : Set E}
    (hAU : A ⊆ U) (hAV : A ⊆ V) (hA0 : μ A ≠ 0) (hAtop : μ A ≠ ⊤)
    {p : ℝ≥0∞} (hp : 1 ≤ p) (hptop : p ≠ ⊤) (e₁ e₂ : ℝ≥0∞)
    (hfirst : eLpNorm (fun x => f x - c) p (μ.restrict U) ≤ e₁ * μ A ^ (1 / p.toReal))
    (hsecond : eLpNorm (fun x => f x - d) p (μ.restrict V) ≤ e₂ * μ A ^ (1 / p.toReal)) :
    ENNReal.ofReal |c - d| ≤ e₁ + e₂ := by
  let t := μ A ^ (1 / p.toReal)
  have ht0 : t ≠ 0 := by simp [t, ENNReal.rpow_eq_zero_iff, hA0, hAtop]
  have httop : t ≠ ⊤ := ENNReal.rpow_ne_top_of_ne_zero hA0 hAtop
  have hh := (ofReal_abs_sub_mul_measure_rpow_le_eLpNorms μ f c d hAU hAV hp hptop).trans
    (add_le_add hfirst hsecond)
  rw [← add_mul] at hh
  change ENNReal.ofReal |c - d| * t ≤ (e₁ + e₂) * t at hh
  have hc := mul_le_mul_left hh t⁻¹
  simp only [mul_assoc, ENNReal.mul_inv_cancel ht0 httop, mul_one] at hc
  exact hc

end HeatKernel

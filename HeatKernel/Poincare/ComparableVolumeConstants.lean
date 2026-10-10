-- Copyright (c) 2026 Scott Armstrong and Amélie Loher. All rights reserved.
-- Released under Apache 2.0 license as described in the file LICENSE.
module

public import HeatKernel.Poincare.NormalizedConstants

/-! Neighboring averaging constants under comparable reference volumes. -/

@[expose] public section
set_option autoImplicit false
set_option relaxedAutoImplicit false
noncomputable section
open Set MeasureTheory
open scoped ENNReal

namespace HeatKernel

/-- Comparing the second reference volume to the common subset converts its oscillation
cost to the first volume scale before the triangle estimate is normalized. -/
theorem ofReal_abs_sub_le_of_comparable_volume_eLpNorm_bounds
    {E : Type*} [MeasurableSpace E] (μ : Measure E) (f : E → ℝ) (c d : ℝ)
    {A U V : Set E} (hAU : A ⊆ U) (hAV : A ⊆ V)
    (hA0 : μ A ≠ 0) (hAtop : μ A ≠ ⊤) {p : ℝ≥0∞} (hp : 1 ≤ p) (hptop : p ≠ ⊤)
    (e₁ e₂ v D : ℝ≥0∞) (hvolume : v ≤ D * μ A)
    (hfirst : eLpNorm (fun x => f x - c) p (μ.restrict U) ≤ e₁ * μ A ^ (1 / p.toReal))
    (hsecond : eLpNorm (fun x => f x - d) p (μ.restrict V) ≤ e₂ * v ^ (1 / p.toReal)) :
    ENNReal.ofReal |c - d| ≤ e₁ + e₂ * D ^ (1 / p.toReal) := by
  apply ofReal_abs_sub_le_of_common_volume_eLpNorm_bounds μ f c d hAU hAV hA0 hAtop
    hp hptop e₁ (e₂ * D ^ (1 / p.toReal)) hfirst
  have hr : 0 ≤ 1 / p.toReal := one_div_nonneg.mpr ENNReal.toReal_nonneg
  have hv := ENNReal.rpow_le_rpow hvolume hr
  rw [ENNReal.mul_rpow_of_nonneg _ _ hr] at hv
  exact hsecond.trans (by simpa only [mul_assoc] using mul_le_mul_right hv e₂)

end HeatKernel

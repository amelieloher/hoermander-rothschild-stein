-- Copyright (c) 2026 Scott Armstrong and Amélie Loher. All rights reserved.
-- Released under Apache 2.0 license as described in the file LICENSE.
module

public import HeatKernel.Poincare.GradientAlongCurve
public import HeatKernel.Poincare.IntegralPower

/-! Power estimates for endpoint oscillation along horizontal curves. -/

@[expose] public section
set_option autoImplicit false
set_option relaxedAutoImplicit false
noncomputable section
open Set MeasureTheory
open scoped BigOperators ENNReal

namespace HeatKernel

/-- The gradient to any positive power is integrable along a compact horizontal curve. -/
theorem IsHorizontalCurveOn.integrableOn_horizontalGradient_rpow {N q : ℕ}
    {X : Fin q → (Fin N → ℝ) → (Fin N → ℝ)} {γ : ℝ → (Fin N → ℝ)}
    {a : Fin q → ℝ → ℝ} {s t p : ℝ} {f : (Fin N → ℝ) → ℝ}
    (h : IsHorizontalCurveOn X γ a s t) (hX : ∀ i, Continuous (X i))
    (hf : ∀ x ∈ γ '' uIcc s t, ContDiffAt ℝ 1 f x) (hp : 0 ≤ p) :
    IntegrableOn (fun r => (Real.sqrt
      (∑ i, (fderiv ℝ f (γ r) (X i (γ r))) ^ 2)) ^ p) (Icc s t) :=
  (((Real.continuous_rpow_const hp).comp_continuousOn
    (h.continuousOn_horizontalGradient hX hf)).mono Icc_subset_uIcc).integrableOn_compact isCompact_Icc

/-- The endpoint oscillation to power p is bounded by interval length to power p−1 times
the integrated horizontal gradient to power p. This includes p=1 directly. -/
theorem IsHorizontalCurveOn.abs_sub_rpow_le_integral_horizontalGradient_rpow {N q : ℕ}
    {X : Fin q → (Fin N → ℝ) → (Fin N → ℝ)} {γ : ℝ → (Fin N → ℝ)}
    {a : Fin q → ℝ → ℝ} {s t p : ℝ} {f : (Fin N → ℝ) → ℝ}
    (h : IsHorizontalCurveOn X γ a s t) (hst : s < t) (hX : ∀ i, Continuous (X i))
    (hf : ∀ x ∈ γ '' uIcc s t, ContDiffAt ℝ 1 f x)
    (ha : ∀ᵐ r ∂volume.restrict (Icc s t), controlNorm a r ≤ 1) (hp : 1 ≤ p) :
    |f (γ t) - f (γ s)| ^ p ≤ (t - s) ^ (p - 1) *
      ∫ r in Icc s t, (Real.sqrt (∑ i, (fderiv ℝ f (γ r) (X i (γ r))) ^ 2)) ^ p := by
  have hp0 : 0 ≤ p := le_trans zero_le_one hp
  have : Fact (volume (Icc s t) < ⊤) := ⟨measure_Icc_lt_top⟩
  have : NeZero (volume.restrict (Icc s t)) := ⟨by
    rw [Ne, Measure.restrict_eq_zero, Real.volume_Icc]
    exact (ENNReal.ofReal_pos.mpr (sub_pos.mpr hst)).ne'⟩
  let g : ℝ → ℝ := fun r => Real.sqrt (∑ i, (fderiv ℝ f (γ r) (X i (γ r))) ^ 2)
  have hg : ∀ r, 0 ≤ g r := fun r => Real.sqrt_nonneg _
  have hgi : IntegrableOn g (Icc s t) := h.integrableOn_horizontalGradient hX hf
  have hgpi : IntegrableOn (fun r => |g r| ^ p) (Icc s t) := by
    simpa only [abs_of_nonneg (hg _)] using h.integrableOn_horizontalGradient_rpow hX hf hp0
  have hj := abs_integral_rpow_le_measure_rpow_mul_integral hp hgi hgpi
  simp only [measureReal_restrict_apply_univ, Real.volume_real_Icc_of_le hst.le,
    abs_of_nonneg (hg _)] at hj
  apply (Real.rpow_le_rpow (abs_nonneg _)
    (h.abs_sub_le_integral_horizontalGradient_of_continuous hst.le hX hf ha) hp0).trans
  simpa only [abs_of_nonneg (integral_nonneg (show 0 ≤ g from hg)), g] using hj

end HeatKernel

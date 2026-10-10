-- Copyright (c) 2026 Scott Armstrong and Amélie Loher. All rights reserved.
-- Released under Apache 2.0 license as described in the file LICENSE.
module

public import HeatKernel.Poincare.HorizontalOscillation

/-! Integrability of the horizontal gradient along a compact horizontal curve. -/

@[expose] public section
set_option autoImplicit false
set_option relaxedAutoImplicit false
noncomputable section
open Set MeasureTheory
open scoped BigOperators

namespace HeatKernel

/-- Continuous fields and a function differentiable continuously near the curve image
make the horizontal gradient norm continuous along the parameter interval. -/
theorem IsHorizontalCurveOn.continuousOn_horizontalGradient {N q : ℕ}
    {X : Fin q → (Fin N → ℝ) → (Fin N → ℝ)} {γ : ℝ → (Fin N → ℝ)}
    {a : Fin q → ℝ → ℝ} {s t : ℝ} {f : (Fin N → ℝ) → ℝ}
    (h : IsHorizontalCurveOn X γ a s t) (hX : ∀ i, Continuous (X i))
    (hf : ∀ x ∈ γ '' uIcc s t, ContDiffAt ℝ 1 f x) :
    ContinuousOn (fun r => Real.sqrt
      (∑ i, (fderiv ℝ f (γ r) (X i (γ r))) ^ 2)) (uIcc s t) := by
  apply Real.continuous_sqrt.comp_continuousOn
  apply continuousOn_finsetSum
  intro i _
  apply ContinuousOn.pow
  intro r hr
  have hc := h.absolutelyContinuous.continuousOn r hr
  exact (((hf (γ r) ⟨r, hr, rfl⟩).continuousAt_fderiv (by norm_num)).comp_continuousWithinAt hc).clm_apply
    ((hX i).continuousAt.comp_continuousWithinAt hc)

/-- The horizontal gradient norm is integrable along every compact horizontal curve
on whose image the function is continuously differentiable. -/
theorem IsHorizontalCurveOn.integrableOn_horizontalGradient {N q : ℕ}
    {X : Fin q → (Fin N → ℝ) → (Fin N → ℝ)} {γ : ℝ → (Fin N → ℝ)}
    {a : Fin q → ℝ → ℝ} {s t : ℝ} {f : (Fin N → ℝ) → ℝ}
    (h : IsHorizontalCurveOn X γ a s t) (hX : ∀ i, Continuous (X i))
    (hf : ∀ x ∈ γ '' uIcc s t, ContDiffAt ℝ 1 f x) :
    IntegrableOn (fun r => Real.sqrt
      (∑ i, (fderiv ℝ f (γ r) (X i (γ r))) ^ 2)) (Icc s t) :=
  ((h.continuousOn_horizontalGradient hX hf).mono Icc_subset_uIcc).integrableOn_compact isCompact_Icc

/-- Unit-speed horizontal curves bound endpoint oscillation by the integrated gradient,
with integrability supplied by continuous differentiability near the curve image. -/
theorem IsHorizontalCurveOn.abs_sub_le_integral_horizontalGradient_of_continuous {N q : ℕ}
    {X : Fin q → (Fin N → ℝ) → (Fin N → ℝ)} {γ : ℝ → (Fin N → ℝ)}
    {a : Fin q → ℝ → ℝ} {s t : ℝ} {f : (Fin N → ℝ) → ℝ}
    (h : IsHorizontalCurveOn X γ a s t) (hst : s ≤ t) (hX : ∀ i, Continuous (X i))
    (hf : ∀ x ∈ γ '' uIcc s t, ContDiffAt ℝ 1 f x)
    (ha : ∀ᵐ r ∂volume.restrict (Icc s t), controlNorm a r ≤ 1) :
    |f (γ t) - f (γ s)| ≤ ∫ r in Icc s t,
      Real.sqrt (∑ i, (fderiv ℝ f (γ r) (X i (γ r))) ^ 2) :=
  h.abs_sub_le_integral_horizontalGradient hst hf ha (h.integrableOn_horizontalGradient hX hf)

end HeatKernel

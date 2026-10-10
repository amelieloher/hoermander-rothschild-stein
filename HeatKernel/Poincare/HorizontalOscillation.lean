-- Copyright (c) 2026 Scott Armstrong and Amélie Loher. All rights reserved.
-- Released under Apache 2.0 license as described in the file LICENSE.
module

public import HeatKernel.Geometry.HorizontalChainRule
public import Mathlib.MeasureTheory.Integral.IntervalIntegral.AbsolutelyContinuousFun

/-! Fundamental theorem of calculus and oscillation estimates along horizontal curves. -/

@[expose] public section
set_option autoImplicit false
set_option relaxedAutoImplicit false
noncomputable section
open Set MeasureTheory
open scoped BigOperators

namespace HeatKernel

/-- An integrable majorant for the horizontal derivative bounds endpoint oscillation.
The majorant is an explicit input, permitting subsequent gradient estimates to be reused. -/
theorem IsHorizontalCurveOn.abs_sub_le_integral_of_horizontalDerivative_le {N q : ℕ}
    {X : Fin q → (Fin N → ℝ) → (Fin N → ℝ)} {γ : ℝ → (Fin N → ℝ)}
    {a : Fin q → ℝ → ℝ} {s t : ℝ} {f : (Fin N → ℝ) → ℝ} {g : ℝ → ℝ}
    (h : IsHorizontalCurveOn X γ a s t) (hst : s ≤ t)
    (hf : ∀ x ∈ γ '' uIcc s t, ContDiffAt ℝ 1 f x)
    (hg : IntegrableOn g (Icc s t))
    (hbound : ∀ᵐ r ∂volume.restrict (Icc s t),
      |∑ i, a i r * fderiv ℝ f (γ r) (X i (γ r))| ≤ g r) :
    |f (γ t) - f (γ s)| ≤ ∫ r in Icc s t, g r := by
  have hc := h.absolutelyContinuous_comp hf
  have hi : IntegrableOn (deriv (f ∘ γ)) (Icc s t) :=
    (intervalIntegrable_iff_integrableOn_Icc_of_le hst).1 hc.intervalIntegrable_deriv
  have hb : ∀ᵐ r ∂volume.restrict (Icc s t), |deriv (f ∘ γ) r| ≤ g r := by
    filter_upwards [h.hasDerivAt_comp hf, hbound] with r hr hb
    simpa only [hr.deriv] using hb
  calc
    |f (γ t) - f (γ s)| = |∫ r in Icc s t, deriv (f ∘ γ) r| := by
      rw [integral_Icc_eq_integral_Ioc, ← intervalIntegral.integral_of_le hst,
        hc.integral_deriv_eq_sub]
      rfl
    _ ≤ ∫ r in Icc s t, |deriv (f ∘ γ) r| := by
      simpa only [Real.norm_eq_abs] using norm_integral_le_integral_norm
        (f := deriv (f ∘ γ)) (μ := volume.restrict (Icc s t))
    _ ≤ ∫ r in Icc s t, g r := integral_mono_ae hi.abs hg hb

/-- Cauchy–Schwarz controls the absolute horizontal pairing by Euclidean norms. -/
theorem abs_sum_mul_le_controlNorm {q : ℕ} (a : Fin q → ℝ → ℝ)
    (b : Fin q → ℝ) (r : ℝ) :
    |∑ i, a i r * b i| ≤ controlNorm a r * Real.sqrt (∑ i, b i ^ 2) := by
  have hp := Real.sum_mul_le_sqrt_mul_sqrt Finset.univ (fun i => a i r) b
  have hn := Real.sum_mul_le_sqrt_mul_sqrt Finset.univ (fun i => -(a i r)) b
  simp only [neg_mul, Finset.sum_neg_distrib, neg_sq] at hp hn
  exact abs_le.mpr ⟨neg_le.mp hn, hp⟩

/-- A curve with control speed at most one has oscillation bounded by the integrated
horizontal gradient norm, whenever that norm is integrable along the curve. -/
theorem IsHorizontalCurveOn.abs_sub_le_integral_horizontalGradient {N q : ℕ}
    {X : Fin q → (Fin N → ℝ) → (Fin N → ℝ)} {γ : ℝ → (Fin N → ℝ)}
    {a : Fin q → ℝ → ℝ} {s t : ℝ} {f : (Fin N → ℝ) → ℝ}
    (h : IsHorizontalCurveOn X γ a s t) (hst : s ≤ t)
    (hf : ∀ x ∈ γ '' uIcc s t, ContDiffAt ℝ 1 f x)
    (ha : ∀ᵐ r ∂volume.restrict (Icc s t), controlNorm a r ≤ 1)
    (hi : IntegrableOn (fun r => Real.sqrt
      (∑ i, (fderiv ℝ f (γ r) (X i (γ r))) ^ 2)) (Icc s t)) :
    |f (γ t) - f (γ s)| ≤ ∫ r in Icc s t,
      Real.sqrt (∑ i, (fderiv ℝ f (γ r) (X i (γ r))) ^ 2) := by
  apply h.abs_sub_le_integral_of_horizontalDerivative_le hst hf hi
  filter_upwards [ha] with r hr
  exact (abs_sum_mul_le_controlNorm a (fun i => fderiv ℝ f (γ r) (X i (γ r))) r).trans
    (by simpa only [one_mul] using mul_le_mul_of_nonneg_right hr (Real.sqrt_nonneg _))

end HeatKernel

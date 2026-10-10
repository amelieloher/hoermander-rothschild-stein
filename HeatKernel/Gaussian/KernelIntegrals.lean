-- Copyright (c) 2026 Scott Armstrong and Amélie Loher. All rights reserved.
-- Released under Apache 2.0 license as described in the file LICENSE.
module

public import Mathlib.MeasureTheory.Integral.Bochner.Basic
import Mathlib.Tactic

/-! # Real and nonnegative kernel integrals

Unit nonnegative mass gives row integrability. Symmetry turns equal-time
convolution into the square-row identity, while nonnegative integral conversion
transfers the real convolution law to lower integrals.
-/

@[expose] public section
set_option autoImplicit false
set_option relaxedAutoImplicit false
open MeasureTheory
open scoped ENNReal
namespace HeatKernel.Gaussian

/-- A measurable nonnegative function of unit mass is integrable. -/
theorem integrable_of_nonnegative_mass_one {α : Type*} [MeasurableSpace α]
    (μ : Measure α) (f : α → ℝ) (hf : AEStronglyMeasurable f μ)
    (hn : ∀ x, 0 ≤ f x) (hm : ∫⁻ x, ENNReal.ofReal (f x) ∂μ = 1) : Integrable f μ := by
  apply (lintegral_ofReal_ne_top_iff_integrable hf (Filter.Eventually.of_forall hn)).mp
  rw [hm]
  exact ENNReal.one_ne_top

/-- A real convolution identity for nonnegative functions transfers to the
product of their nonnegative extended-real values. -/
theorem lintegral_ofReal_mul_eq_of_integral {α : Type*} [MeasurableSpace α]
    (μ : Measure α) (f g : α → ℝ) (hf : ∀ x, 0 ≤ f x) (hg : ∀ x, 0 ≤ g x)
    (hfg : Integrable (fun x => f x * g x) μ) {a : ℝ}
    (hint : (∫ x, f x * g x ∂μ) = a) :
    (∫⁻ x, ENNReal.ofReal (f x) * ENNReal.ofReal (g x) ∂μ) = ENNReal.ofReal a := by
  calc
    _ = ∫⁻ x, ENNReal.ofReal (f x * g x) ∂μ := by
      apply lintegral_congr
      intro x
      exact (ENNReal.ofReal_mul (hf x)).symm
    _ = ENNReal.ofReal (∫ x, f x * g x ∂μ) :=
      (ofReal_integral_eq_lintegral_ofReal hfg
        (Filter.Eventually.of_forall (fun x => mul_nonneg (hf x) (hg x)))).symm
    _ = _ := congrArg ENNReal.ofReal hint

/-- Nonnegative real kernels with integrable convolution products satisfy the
same pointwise convolution law after conversion to extended-real values. -/
theorem lintegral_kernel_convolution_of_real {α : Type*} [MeasurableSpace α]
    (μ : Measure α) (p : ℝ → α → α → ℝ)
    (hn : ∀ t, 0 < t → ∀ x y, 0 ≤ p t x y)
    (hi : ∀ s t, 0 < s → 0 < t → ∀ x y,
      Integrable (fun z => p s x z * p t z y) μ)
    (hconv : ∀ s t, 0 < s → 0 < t → ∀ x y,
      p (s + t) x y = ∫ z, p s x z * p t z y ∂μ)
    {s t : ℝ} (hs : 0 < s) (ht : 0 < t) (x y : α) :
    ENNReal.ofReal (p (s + t) x y) =
      ∫⁻ z, ENNReal.ofReal (p s x z) * ENNReal.ofReal (p t z y) ∂μ := by
  exact (lintegral_ofReal_mul_eq_of_integral μ (p s x) (fun z => p t z y)
    (hn s hs x) (fun z => hn t ht z y) (hi s t hs ht x y) (hconv s t hs ht x y).symm).symm

end HeatKernel.Gaussian

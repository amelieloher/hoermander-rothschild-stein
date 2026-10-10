-- Copyright (c) 2026 Scott Armstrong and Amélie Loher. All rights reserved.
-- Released under Apache 2.0 license as described in the file LICENSE.
module

public import HeatKernel.Gaussian.KernelIntegrals
public import HeatKernel.Gaussian.HomogeneousBounds
import Mathlib.Tactic

/-! # Kernel integrability from Gaussian upper bounds and unit mass

A Gaussian upper estimate bounds each fixed-time row uniformly. Unit mass then
gives row square integrability and integrability of symmetric convolutions.
-/

@[expose] public section
set_option autoImplicit false
set_option relaxedAutoImplicit false
noncomputable section
open MeasureTheory Set Metric RothschildStein
namespace HeatKernel.Gaussian

/-- A Gaussian upper bound with nonnegative prefactor gives a uniform row bound. -/
theorem le_prefactor_of_gaussian_bound {α : Type*} [PseudoMetricSpace α]
    (f : α → ℝ) (x : α) {a t M : ℝ} (ha : 0 ≤ a) (ht : 0 < t) (hM : 0 ≤ M)
    (hupper : ∀ y, f y ≤ M * Real.exp (-a * (dist x y ^ 2 / t))) :
    ∀ y, f y ≤ M := by
  intro y
  calc
    f y ≤ _ := hupper y
    _ ≤ M * 1 := mul_le_mul_of_nonneg_left
      (Real.exp_le_one_iff.mpr (mul_nonpos_of_nonpos_of_nonneg
        (neg_nonpos.mpr ha) (div_nonneg (sq_nonneg _) ht.le))) hM
    _ = M := mul_one _

/-- Symmetric conservative kernels with measurable rows and Gaussian upper
bounds have integrable convolution products at every positive pair of times. -/
theorem integrable_kernel_convolution_of_gaussian_and_mass {α : Type*}
    [PseudoMetricSpace α] [MeasurableSpace α] (μ : Measure α)
    (p : ℝ → α → α → ℝ) (V : ℝ → α → ℝ) {a U : ℝ} (ha : 0 ≤ a) (hU : 0 ≤ U)
    (hV : ∀ t, 0 < t → ∀ x, 0 ≤ V t x)
    (hmeas : ∀ t, 0 < t → ∀ x, AEStronglyMeasurable (p t x) μ)
    (hn : ∀ t, 0 < t → ∀ x y, 0 ≤ p t x y)
    (hmass : ∀ t, 0 < t → ∀ x, ∫⁻ z, ENNReal.ofReal (p t x z) ∂μ = 1)
    (hsym : ∀ t, 0 < t → ∀ x y, p t x y = p t y x)
    (hupper : ∀ t, 0 < t → ∀ x y,
      p t x y ≤ U / V t x * Real.exp (-a * (dist x y ^ 2 / t)))
    {s t : ℝ} (hs : 0 < s) (ht : 0 < t) (x y : α) :
    Integrable (fun z ↦ p s x z * p t z y) μ := by
  have hi := integrable_of_nonnegative_mass_one μ (p t y) (hmeas t ht y)
    (hn t ht y) (hmass t ht y)
  have hb := le_prefactor_of_gaussian_bound (p s x) x ha hs
    (div_nonneg hU (hV s hs x)) (hupper s hs x)
  have H := hi.bdd_mul (hmeas s hs x) (Filter.Eventually.of_forall (fun z ↦ by
    rw [Real.norm_eq_abs, abs_of_nonneg (hn s hs x z)]
    exact hb z))
  convert H using 1
  funext z
  rw [hsym t ht z y]

end HeatKernel.Gaussian

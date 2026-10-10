-- Copyright (c) 2026 Scott Armstrong and Amélie Loher. All rights reserved.
-- Released under Apache 2.0 license as described in the file LICENSE.
module

public import HeatKernel.Gaussian.ConjugatedEnergy
import Mathlib.Tactic

/-! # Weighted norm and horizontal energy identities

Exponential multiplication realizes the weighted square integral exactly.
The horizontal completion of the square controls a weighted form identity by
the weighted Hilbert norm.
-/

@[expose] public section
set_option autoImplicit false
set_option relaxedAutoImplicit false
noncomputable section
open MeasureTheory
open scoped BigOperators
namespace HeatKernel.Gaussian

/-- The norm of exponential multiplication is the literal weighted square integral. -/
theorem norm_sq_exponentialMultiplication_eq_integral {α : Type*} [MeasurableSpace α]
    (μ : Measure α) (ψ : α → ℝ) (hψ : AEStronglyMeasurable ψ μ) (B : ℝ)
    (hB : ∀ x, |ψ x| ≤ B) (a : ℝ) (f : Lp ℝ 2 μ) :
    ‖exponentialMultiplication μ ψ hψ B hB a f‖ ^ 2 =
      ∫ x, Real.exp (2 * a * ψ x) * f x ^ 2 ∂μ := by
  rw [← real_inner_self_eq_norm_sq, L2.inner_def]
  apply integral_congr_ae
  filter_upwards [coeFn_exponentialMultiplication μ ψ hψ B hB a f] with x hx
  rw [hx]
  change (Real.exp (a * ψ x) * f x) * (Real.exp (a * ψ x) * f x) = _
  have he : Real.exp (2 * a * ψ x) = Real.exp (a * ψ x) * Real.exp (a * ψ x) := by
    rw [← Real.exp_add]
    congr 1
    ring
  rw [he]
  ring

/-- A horizontal form identity and a unit weak-gradient bound give the weighted
inner-product estimate needed for the energy trajectory. -/
theorem inner_exponential_le_of_horizontal_form_identity {α ι : Type*}
    [MeasurableSpace α] [Fintype ι] (μ : Measure α)
    (ψ : α → ℝ) (hψ : AEStronglyMeasurable ψ μ) (B : ℝ)
    (hB : ∀ x, |ψ x| ≤ B) (a : ℝ) (u v : Lp ℝ 2 μ)
    (g h : α → ι → ℝ)
    (hh : ∀ᵐ x ∂μ, ∑ i, h x i ^ 2 ≤ 1)
    (hg : Integrable (fun x ↦ Real.exp (2 * a * ψ x) *
      ∑ i, g x i * (g x i + 2 * a * u x * h x i)) μ)
    (hidentity : inner ℝ (exponentialMultiplication μ ψ hψ B hB a u)
      (exponentialMultiplication μ ψ hψ B hB a v) =
        -(∫ x, Real.exp (2 * a * ψ x) *
          ∑ i, g x i * (g x i + 2 * a * u x * h x i) ∂μ)) :
    inner ℝ (exponentialMultiplication μ ψ hψ B hB a u)
      (exponentialMultiplication μ ψ hψ B hB a v) ≤
        a ^ 2 * ‖exponentialMultiplication μ ψ hψ B hB a u‖ ^ 2 := by
  have hu : Integrable (fun x ↦ Real.exp (2 * a * ψ x) * u x ^ 2) μ := by
    apply (Lp.memLp u).integrable_sq.bdd_mul
      (Real.continuous_exp.comp_aestronglyMeasurable (aestronglyMeasurable_const.mul hψ))
    exact Filter.Eventually.of_forall (fun x ↦ norm_exp_mul_le_of_abs_le (a := 2 * a) (hB x))
  rw [hidentity, norm_sq_exponentialMultiplication_eq_integral,
    ← integral_neg, ← integral_const_mul]
  apply integral_mono_ae hg.neg (hu.const_mul _)
  filter_upwards [hh] with x hx
  change -(Real.exp (2 * a * ψ x) *
    ∑ i, g x i * (g x i + 2 * a * u x * h x i)) ≤
      a ^ 2 * (Real.exp (2 * a * ψ x) * u x ^ 2)
  have H := neg_two_weighted_gradient_le (g x) (h x) a (u x) hx
  have H' : -(∑ i, g x i * (g x i + 2 * a * u x * h x i)) ≤ a ^ 2 * u x ^ 2 := by
    linarith
  calc
    _ = Real.exp (2 * a * ψ x) *
        (-(∑ i, g x i * (g x i + 2 * a * u x * h x i))) := by ring
    _ ≤ Real.exp (2 * a * ψ x) * (a ^ 2 * u x ^ 2) :=
      mul_le_mul_of_nonneg_left H' (Real.exp_pos _).le
    _ = _ := by ring

end HeatKernel.Gaussian

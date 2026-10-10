-- Copyright (c) 2026 Scott Armstrong and Amélie Loher. All rights reserved.
-- Released under Apache 2.0 license as described in the file LICENSE.
module

public import HeatKernel.Gaussian.WeightedEnergyIdentity
public import HeatKernel.Gaussian.WeightedDatum
import Mathlib.Tactic

/-! # Weighted integral estimates from exponential conjugation

The conjugated operator bound controls weighted square integrals of the
actual L² evolution. Compact normalized data give an explicit initial factor.
-/

@[expose] public section
set_option autoImplicit false
set_option relaxedAutoImplicit false
noncomputable section
open MeasureTheory Set
namespace HeatKernel.Gaussian

/-- Exponential conjugation controls the literal weighted square integral of an
L² evolution by its weighted initial square integral. -/
theorem integral_weighted_sq_evolution_le_of_conjugation {α : Type*}
    [MeasurableSpace α] (μ : Measure α) (ψ : α → ℝ)
    (hψ : AEStronglyMeasurable ψ μ) (B : ℝ) (hB : ∀ x, |ψ x| ≤ B)
    (T : Lp ℝ 2 μ →L[ℝ] Lp ℝ 2 μ) (f : Lp ℝ 2 μ) {a t : ℝ}
    (hweighted : ‖(exponentialMultiplication μ ψ hψ B hB a).comp
      (T.comp (exponentialMultiplication μ ψ hψ B hB (-a)))‖ ≤ Real.exp (a ^ 2 * t)) :
    (∫ x, Real.exp (2 * a * ψ x) * T f x ^ 2 ∂μ) ≤
      Real.exp (2 * a ^ 2 * t) * ∫ x, Real.exp (2 * a * ψ x) * f x ^ 2 ∂μ := by
  rw [← norm_sq_exponentialMultiplication_eq_integral μ ψ hψ B hB a (T f),
    ← norm_sq_exponentialMultiplication_eq_integral μ ψ hψ B hB a f]
  let M := exponentialMultiplication μ ψ hψ B hB a
  let N := exponentialMultiplication μ ψ hψ B hB (-a)
  have hNM : N (M f) = f := by
    have H := congrArg (fun L : Lp ℝ 2 μ →L[ℝ] Lp ℝ 2 μ ↦ L f)
      (exponentialMultiplication_comp_neg_eq_id μ ψ hψ B hB (-a))
    simpa only [neg_neg, ContinuousLinearMap.comp_apply, ContinuousLinearMap.id_apply] using H
  have H : ‖M (T f)‖ ≤ Real.exp (a ^ 2 * t) * ‖M f‖ := by
    calc
      _ = ‖(M.comp (T.comp N)) (M f)‖ := by simp only [ContinuousLinearMap.comp_apply, hNM]
      _ ≤ ‖M.comp (T.comp N)‖ * ‖M f‖ := ContinuousLinearMap.le_opNorm _ _
      _ ≤ Real.exp (a ^ 2 * t) * ‖M f‖ := mul_le_mul_of_nonneg_right hweighted (norm_nonneg _)
  have Hsq := (sq_le_sq₀ (norm_nonneg (M (T f))) (by positivity)).mpr H
  have he : Real.exp (a ^ 2 * t) ^ 2 = Real.exp (2 * a ^ 2 * t) := by
    rw [pow_two, ← Real.exp_add]
    congr 1
    ring
  rw [mul_pow, he] at Hsq
  exact Hsq

/-- A represented evolution of normalized compact data has weighted square
integral controlled by the logarithmic weight bound on its support. -/
theorem integral_weighted_normalized_evolution_le {α : Type*} [MeasurableSpace α]
    (μ : Measure α) (ψ : α → ℝ) (hψ : AEStronglyMeasurable ψ μ)
    (B : ℝ) (hB : ∀ x, |ψ x| ≤ B)
    {S : Set α} (hS : MeasurableSet S) (f : α → ℝ) (hf : AEStronglyMeasurable f μ)
    (hpos : 0 < ∫ z in S, f z ^ 2 ∂μ)
    (T : Lp ℝ 2 μ →L[ℝ] Lp ℝ 2 μ) (v : α → ℝ) {a t L : ℝ}
    (hv : v =ᵐ[μ] T ((memLp_normalized_indicator μ hS f hf hpos).toLp
      (S.indicator (fun z ↦ f z / Real.sqrt (∫ w in S, f w ^ 2 ∂μ)))))
    (hlocal : ∀ z ∈ S, 2 * a * ψ z ≤ L)
    (hweighted : ‖(exponentialMultiplication μ ψ hψ B hB a).comp
      (T.comp (exponentialMultiplication μ ψ hψ B hB (-a)))‖ ≤ Real.exp (a ^ 2 * t)) :
    (∫ z, Real.exp (2 * a * ψ z) * v z ^ 2 ∂μ) ≤ Real.exp (2 * a ^ 2 * t + L) := by
  let g := S.indicator (fun z ↦ f z / Real.sqrt (∫ w in S, f w ^ 2 ∂μ))
  let hg := memLp_normalized_indicator μ hS f hf hpos
  let u := hg.toLp g
  have hinit : (∫ z, Real.exp (2 * a * ψ z) * g z ^ 2 ∂μ) ≤ Real.exp L := by
    apply integral_weighted_sq_normalized_indicator_le μ hS f (fun z ↦ 2 * a * ψ z) hpos
      (aestronglyMeasurable_const.mul hψ) (B := 2 * |a| * B) _ hlocal
    intro z
    have H : a * ψ z ≤ |a| * B := by
      calc
        _ ≤ |a * ψ z| := le_abs_self _
        _ = |a| * |ψ z| := abs_mul _ _
        _ ≤ |a| * B := mul_le_mul_of_nonneg_left (hB z) (abs_nonneg _)
    linarith
  have heq : (∫ z, Real.exp (2 * a * ψ z) * u z ^ 2 ∂μ) =
      ∫ z, Real.exp (2 * a * ψ z) * g z ^ 2 ∂μ := by
    apply integral_congr_ae
    filter_upwards [hg.coeFn_toLp] with z hz
    rw [hz]
  calc
    _ = ∫ z, Real.exp (2 * a * ψ z) * T u z ^ 2 ∂μ := by
      apply integral_congr_ae
      filter_upwards [hv] with z hz
      rw [hz]
    _ ≤ Real.exp (2 * a ^ 2 * t) * ∫ z, Real.exp (2 * a * ψ z) * u z ^ 2 ∂μ :=
      integral_weighted_sq_evolution_le_of_conjugation μ ψ hψ B hB T u hweighted
    _ = Real.exp (2 * a ^ 2 * t) * ∫ z, Real.exp (2 * a * ψ z) * g z ^ 2 ∂μ := by rw [heq]
    _ ≤ Real.exp (2 * a ^ 2 * t) * Real.exp L :=
      mul_le_mul_of_nonneg_left hinit (Real.exp_pos _).le
    _ = _ := (Real.exp_add _ _).symm

end HeatKernel.Gaussian

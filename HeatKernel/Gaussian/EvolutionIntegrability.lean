-- Copyright (c) 2026 Scott Armstrong and Amélie Loher. All rights reserved.
-- Released under Apache 2.0 license as described in the file LICENSE.
module

public import HeatKernel.Gaussian.DistanceExponentialOperator
import Mathlib.Tactic

/-! # Integrability of represented weighted evolutions

An L² representative has integrable square after multiplication by a bounded
exponential weight. Restriction to an endpoint ball preserves integrability.
-/

@[expose] public section
set_option autoImplicit false
set_option relaxedAutoImplicit false
noncomputable section
open MeasureTheory Set Metric
namespace HeatKernel.Gaussian

/-- A bounded measurable exponential weight preserves integrability of the
square of any representative of an L² function. -/
theorem integrable_weighted_sq_of_l2_representative {X : Type*} [MeasurableSpace X]
    (μ : Measure X) (ψ : X → ℝ) (hψ : AEStronglyMeasurable ψ μ)
    (B : ℝ) (hB : ∀ x, |ψ x| ≤ B) (a : ℝ) (f : Lp ℝ 2 μ)
    (v : X → ℝ) (hv : v =ᵐ[μ] f) :
    Integrable (fun x ↦ Real.exp (2 * a * ψ x) * v x ^ 2) μ := by
  have H : Integrable (fun x ↦ Real.exp (2 * a * ψ x) * f x ^ 2) μ := by
    apply (Lp.memLp f).integrable_sq.bdd_mul
      (Real.continuous_exp.comp_aestronglyMeasurable (aestronglyMeasurable_const.mul hψ))
    exact Filter.Eventually.of_forall (fun x ↦ norm_exp_mul_le_of_abs_le (a := 2 * a) (hB x))
  apply H.congr
  filter_upwards [hv] with x hx
  rw [hx]

/-- Every representative of an L² function has integrable square on every set. -/
theorem integrableOn_sq_of_l2_representative {X : Type*} [MeasurableSpace X]
    (μ : Measure X) (f : Lp ℝ 2 μ) (v : X → ℝ) (hv : v =ᵐ[μ] f) (S : Set X) :
    IntegrableOn (fun x ↦ v x ^ 2) S μ := by
  have H : Integrable (fun x ↦ v x ^ 2) μ := by
    apply (Lp.memLp f).integrable_sq.congr
    filter_upwards [hv] with x hx
    rw [hx]
  exact H.integrableOn

/-- Distance-weighted square integrability follows directly from an L²
representation, with no additional local regularity assumption. -/
theorem integrable_distance_weighted_sq_of_l2_representative {X : Type*}
    [PseudoMetricSpace X] [MeasurableSpace X] [BorelSpace X]
    (μ : Measure X) (x y : X) (a : ℝ) (f : Lp ℝ 2 μ)
    (v : X → ℝ) (hv : v =ᵐ[μ] f) :
    Integrable (fun z ↦ Real.exp (2 * a * min (dist x z) (dist x y)) * v z ^ 2) μ :=
  integrable_weighted_sq_of_l2_representative μ _
    (lipschitzWith_truncated_distance x y).continuous.aestronglyMeasurable
    (dist x y) (abs_truncated_distance_le x y) a f v hv

end HeatKernel.Gaussian

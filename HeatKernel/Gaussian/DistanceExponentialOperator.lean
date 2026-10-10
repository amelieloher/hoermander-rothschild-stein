-- Copyright (c) 2026 Scott Armstrong and Amélie Loher. All rights reserved.
-- Released under Apache 2.0 license as described in the file LICENSE.
module

public import HeatKernel.Gaussian.WeightedEvolution
public import HeatKernel.Gaussian.TruncatedDistance
import Mathlib.Tactic

/-! # Exponential operators for bounded distance weights

Truncated distance gives canonical bounded exponential operators on metric
measure spaces. Their normalized evolutions have the explicit initial loss
used in the endpoint estimate.
-/

@[expose] public section
set_option autoImplicit false
set_option relaxedAutoImplicit false
noncomputable section
open MeasureTheory Set Metric
namespace HeatKernel.Gaussian

/-- The absolute truncated distance is bounded by the center separation. -/
theorem abs_truncated_distance_le {X : Type*} [PseudoMetricSpace X] (x y z : X) :
    |min (dist x z) (dist x y)| ≤ dist x y := by
  rw [abs_of_nonneg (truncated_distance_bounds x y z).1]
  exact (truncated_distance_bounds x y z).2

/-- Exponential multiplication for the bounded distance weight of two centers. -/
def distanceExponentialMultiplication {X : Type*} [PseudoMetricSpace X]
    [MeasurableSpace X] [BorelSpace X] (μ : Measure X) (x y : X) (a : ℝ) :
    Lp ℝ 2 μ →L[ℝ] Lp ℝ 2 μ :=
  exponentialMultiplication μ (fun z ↦ min (dist x z) (dist x y))
    (lipschitzWith_truncated_distance x y).continuous.aestronglyMeasurable
    (dist x y) (abs_truncated_distance_le x y) a

/-- The distance exponential operator acts by its literal pointwise weight. -/
theorem coeFn_distanceExponentialMultiplication {X : Type*} [PseudoMetricSpace X]
    [MeasurableSpace X] [BorelSpace X] (μ : Measure X) (x y : X) (a : ℝ) (f : Lp ℝ 2 μ) :
    distanceExponentialMultiplication μ x y a f =ᵐ[μ]
      fun z ↦ Real.exp (a * min (dist x z) (dist x y)) * f z :=
  coeFn_exponentialMultiplication μ _ _ _ _ a f

/-- The represented evolution of a normalized row on the first endpoint ball
has weighted energy at most exp(2β²t + 4βr). -/
theorem integral_distance_weighted_normalized_evolution_le {X : Type*} [PseudoMetricSpace X]
    [MeasurableSpace X] [BorelSpace X] (μ : Measure X) (x y : X)
    (f : X → ℝ) (hf : AEStronglyMeasurable f μ) {r β t : ℝ} (hβ : 0 ≤ β)
    (hpos : 0 < ∫ z in ball x (2 * r), f z ^ 2 ∂μ)
    (T : Lp ℝ 2 μ →L[ℝ] Lp ℝ 2 μ) (v : X → ℝ)
    (hv : v =ᵐ[μ] T ((memLp_normalized_indicator μ measurableSet_ball f hf hpos).toLp
      ((ball x (2 * r)).indicator (fun z ↦ f z /
        Real.sqrt (∫ w in ball x (2 * r), f w ^ 2 ∂μ)))))
    (hweighted : ‖(distanceExponentialMultiplication μ x y β).comp
      (T.comp (distanceExponentialMultiplication μ x y (-β)))‖ ≤ Real.exp (β ^ 2 * t)) :
    (∫ z, Real.exp (2 * β * min (dist x z) (dist x y)) * v z ^ 2 ∂μ) ≤
      Real.exp (2 * β ^ 2 * t + 4 * β * r) := by
  apply integral_weighted_normalized_evolution_le μ _
    (lipschitzWith_truncated_distance x y).continuous.aestronglyMeasurable
    (dist x y) (abs_truncated_distance_le x y) measurableSet_ball f hf hpos T v hv ?_ hweighted
  intro z hz
  have H := mul_le_mul_of_nonneg_left (truncated_distance_le_of_mem_ball (y := y) hz)
    (show 0 ≤ 2 * β by positivity)
  nlinarith

end HeatKernel.Gaussian

-- Copyright (c) 2026 Scott Armstrong and Amélie Loher. All rights reserved.
-- Released under Apache 2.0 license as described in the file LICENSE.
module

public import HeatKernel.Gaussian.EvolutionIntegrability
public import HeatKernel.Gaussian.SliceIntegrability
public import HeatKernel.Gaussian.WeightedIntegral
import Mathlib.Tactic

/-! # Endpoint bounds for represented normalized evolutions

A continuous evolution represented by L² operators needs only the exponential
conjugation bound and its mean-value inequality to give the first endpoint
estimate. Square integrability and the distance-weight losses follow directly.
-/

@[expose] public section
set_option autoImplicit false
set_option relaxedAutoImplicit false
noncomputable section
open MeasureTheory Set Metric
namespace HeatKernel.Gaussian

/-- Exponential conjugation and a mean-value inequality give the first endpoint
estimate for the represented evolution of a positive normalized row. -/
theorem integral_row_sq_le_of_represented_normalized_evolution {X : Type*}
    [PseudoMetricSpace X] [ProperSpace X]
    [MeasurableSpace X] [BorelSpace X] [SecondCountableTopology X]
    (μ : Measure X) (x y : X) (f : X → ℝ) (hf : AEStronglyMeasurable f μ)
    (T : ℝ → Lp ℝ 2 μ →L[ℝ] Lp ℝ 2 μ) (v : ℝ × X → ℝ)
    (hv : ContinuousOn v (Ioi 0 ×ˢ univ))
    {t s β C V : ℝ} (ht : 0 < t) (hs : s ∈ Icc (t / 2) (2 * t))
    (hβ : 0 ≤ β) (hV : 0 < V) :
    let r := Real.sqrt t / 4;
    let A := ∫ z in ball x (2 * r), f z ^ 2 ∂μ;
    ∀ hpos : 0 < A,
    let u := (memLp_normalized_indicator μ measurableSet_ball f hf hpos).toLp
      ((ball x (2 * r)).indicator (fun z ↦ f z / Real.sqrt A));
    μ (ball y (2 * r)) ≠ ⊤ →
    (∀ σ > 0, (fun z ↦ v (σ, z)) =ᵐ[μ] T σ u) →
    (∀ σ > 0, ‖(distanceExponentialMultiplication μ x y β).comp
      ((T σ).comp (distanceExponentialMultiplication μ x y (-β)))‖ ≤ Real.exp (β ^ 2 * σ)) →
    (A ≤ C ^ 2 / (r ^ 2 * V) *
      ∫ σ in Ioo (s - 7 * r ^ 2 / 2) (s + r ^ 2 / 2),
        ∫ z in ball y (2 * r), v (σ, z) ^ 2 ∂μ) →
    A ≤ 4 * C ^ 2 / V * Real.exp (-2 * β * dist x y + 8 * β * r + 6 * β ^ 2 * t) := by
  intro r A hpos u hμ hrepr hconj hmean
  have hr : 0 < r := by dsimp [r]; positivity
  have hσpos : ∀ σ ∈ Ioo (s - 7 * r ^ 2 / 2) (s + r ^ 2 / 2), 0 < σ :=
    fun σ hσ ↦ ((endpoint_cylinder_subset_positive ht hs).2 hσ).1
  have htime := integrableOn_endpoint_integral_ball_sq μ y v hv ht hs hμ
  have H := sq_le_of_weighted_energy_mean_value μ measurableSet_ball
    (fun σ z ↦ v (σ, z)) (fun z ↦ 2 * β * min (dist x z) (dist x y))
    (t := t) (C := C) (p := Real.sqrt A) hr hV
    (fun z hz ↦ weighted_sub_radius_le_truncated_distance (by positivity : 0 ≤ 2 * r) hβ hz)
    (fun σ hσ ↦ integrableOn_sq_of_l2_representative μ (T σ u) _
      (hrepr σ (hσpos σ hσ)) _)
    (fun σ hσ ↦ integrable_distance_weighted_sq_of_l2_representative μ x y β (T σ u) _
      (hrepr σ (hσpos σ hσ))) ?_ htime
    (show (Real.sqrt A) ^ 2 ≤ _ by rw [Real.sq_sqrt hpos.le]; exact hmean)
  · simpa only [Real.sq_sqrt hpos.le] using H
  · intro σ hσ
    have he := integral_distance_weighted_normalized_evolution_le μ x y f hf hβ hpos
      (T σ) (fun z ↦ v (σ, z)) (hrepr σ (hσpos σ hσ)) (hconj σ (hσpos σ hσ))
    apply he.trans
    apply Real.exp_le_exp.mpr
    have hσt := ((endpoint_cylinder_subset_positive ht hs).2 hσ).2
    nlinarith [sq_nonneg β]

end HeatKernel.Gaussian

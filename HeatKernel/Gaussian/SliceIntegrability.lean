-- Copyright (c) 2026 Scott Armstrong and Amélie Loher. All rights reserved.
-- Released under Apache 2.0 license as described in the file LICENSE.
module

public import HeatKernel.Gaussian.KernelIntegralContinuity
public import HeatKernel.Gaussian.EndpointBounds
import Mathlib.Tactic

/-! # Integrability of spatial square slices

Joint continuity gives continuous spatial square integrals over finite-measure
balls in a proper space. Positive endpoint cylinders therefore have integrable
time slices.
-/

@[expose] public section
set_option autoImplicit false
set_option relaxedAutoImplicit false
noncomputable section
open MeasureTheory Set Metric
namespace HeatKernel.Gaussian

/-- Spatial square integrals of a jointly continuous function vary continuously
on positive times whenever the spatial ball has finite measure. -/
theorem continuousOn_integral_ball_sq {X : Type*} [PseudoMetricSpace X] [ProperSpace X]
    [MeasurableSpace X] [BorelSpace X] [SecondCountableTopology X]
    (μ : Measure X) (x : X) (R : ℝ) (hμ : μ (ball x R) ≠ ⊤)
    (v : ℝ × X → ℝ) (hv : ContinuousOn v (Ioi 0 ×ˢ univ)) :
    ContinuousOn (fun t ↦ ∫ z in ball x R, v (t, z) ^ 2 ∂μ) (Ioi 0) := by
  let f : X → ℝ := (ball x R).indicator (fun _ ↦ 1)
  have hf : Integrable f μ :=
    (integrableOn_const hμ).integrable_indicator measurableSet_ball
  have hsupp : Function.support f ⊆ closedBall x R := by
    intro z hz
    by_contra hn
    have hz' : z ∉ ball x R := fun h ↦ hn (ball_subset_closedBall h)
    exact hz (by simp [f, hz'])
  have H := continuousOn_kernel_integral_of_compact_data μ hf (isCompact_closedBall x R)
    hsupp isOpen_Ioi (fun p : ℝ × X ↦ v p ^ 2) (hv.pow 2)
  have heq : (fun t ↦ ∫ z, f z • v (t, z) ^ 2 ∂μ) =
      (fun t ↦ ∫ z in ball x R, v (t, z) ^ 2 ∂μ) := by
    funext t
    rw [← integral_indicator measurableSet_ball]
    apply integral_congr_ae
    exact Filter.Eventually.of_forall (fun z ↦ by
      by_cases hz : z ∈ ball x R <;> simp [f, hz])
  rw [heq] at H
  exact H

/-- Every interval with positive lower endpoint has integrable spatial square
slices of a jointly continuous evolution. -/
theorem integrableOn_integral_ball_sq {X : Type*} [PseudoMetricSpace X] [ProperSpace X]
    [MeasurableSpace X] [BorelSpace X] [SecondCountableTopology X]
    (μ : Measure X) (x : X) (R : ℝ) (hμ : μ (ball x R) ≠ ⊤)
    (v : ℝ × X → ℝ) (hv : ContinuousOn v (Ioi 0 ×ˢ univ))
    {a b : ℝ} (ha : 0 < a) :
    IntegrableOn (fun t ↦ ∫ z in ball x R, v (t, z) ^ 2 ∂μ) (Ioo a b) := by
  have H := continuousOn_integral_ball_sq μ x R hμ v hv
  have hc : ContinuousOn (fun t ↦ ∫ z in ball x R, v (t, z) ^ 2 ∂μ) (Icc a b) :=
    H.mono (fun _ ht ↦ lt_of_lt_of_le ha ht.1)
  exact hc.integrableOn_Icc.mono_set Ioo_subset_Icc_self

/-- The endpoint time interval has integrable spatial square slices without
an additional time-integrability hypothesis. -/
theorem integrableOn_endpoint_integral_ball_sq {X : Type*}
    [PseudoMetricSpace X] [ProperSpace X]
    [MeasurableSpace X] [BorelSpace X] [SecondCountableTopology X]
    (μ : Measure X) (y : X) (v : ℝ × X → ℝ)
    (hv : ContinuousOn v (Ioi 0 ×ˢ univ)) {t s : ℝ}
    (ht : 0 < t) (hs : s ∈ Icc (t / 2) (2 * t))
    (hμ : μ (ball y (2 * (Real.sqrt t / 4))) ≠ ⊤) :
    let r := Real.sqrt t / 4;
    IntegrableOn (fun σ ↦ ∫ z in ball y (2 * r), v (σ, z) ^ 2 ∂μ)
      (Ioo (s - 7 * r ^ 2 / 2) (s + r ^ 2 / 2)) :=
  integrableOn_integral_ball_sq μ y _ hμ v hv (endpoint_cylinder_subset_positive ht hs).1

end HeatKernel.Gaussian

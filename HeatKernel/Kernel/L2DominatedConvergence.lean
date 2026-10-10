-- Copyright (c) 2026 Scott Armstrong and Amélie Loher. All rights reserved.
-- Released under Apache 2.0 license as described in the file LICENSE.
module

public import Mathlib.MeasureTheory.Function.L2Space
public import Mathlib.MeasureTheory.Integral.DominatedConvergence

/-! # Dominated convergence for scalar L² classes

Dominated convergence applied to the squares of scalar functions gives
convergence of their L² classes. This also applies to difference quotients
of compact spacetime tests when a square-integrable bound is available.
-/

@[expose] public section

noncomputable section

open MeasureTheory Filter
open scoped Topology

namespace HeatKernel

/-- The norm of a scalar L² class is the square root of the integral of its square. -/
theorem norm_toLp_two_eq_sqrt_integral_sq {α : Type*} [MeasurableSpace α]
    {μ : Measure α} {f : α → ℝ} (hf : MemLp f 2 μ) :
    ‖hf.toLp f‖ = Real.sqrt (∫ x, f x ^ 2 ∂μ) := by
  have hsq : ‖hf.toLp f‖ ^ 2 = ∫ x, f x ^ 2 ∂μ := by
    rw [← real_inner_self_eq_norm_sq, L2.inner_def]
    apply integral_congr_ae
    filter_upwards [hf.coeFn_toLp] with x hx
    simp only [Real.inner_apply, hx, pow_two]
  have h := congrArg Real.sqrt hsq
  rwa [Real.sqrt_sq (norm_nonneg _)] at h

/-- Squared scalar functions converge in integral under a square-integrable pointwise bound. -/
theorem tendsto_integral_sq_zero_of_dominated {α ι : Type*} [MeasurableSpace α]
    {μ : Measure α} {l : Filter ι} [l.IsCountablyGenerated]
    (F : ι → α → ℝ) (hF : ∀ i, AEStronglyMeasurable (F i) μ)
    {g : α → ℝ} (hg : Integrable (fun x => g x ^ 2) μ)
    (hb : ∀ᶠ i in l, ∀ᵐ x ∂μ, ‖F i x‖ ≤ g x)
    (hlim : ∀ᵐ x ∂μ, Tendsto (fun i => F i x) l (𝓝 0)) :
    Tendsto (fun i => ∫ x, (F i x) ^ 2 ∂μ) l (𝓝 (0 : ℝ)) := by
  have hbound : ∀ᶠ i in l, ∀ᵐ x ∂μ, ‖(F i x) ^ 2‖ ≤ g x ^ 2 := by
    filter_upwards [hb] with i hi
    filter_upwards [hi] with x hx
    rw [norm_pow]
    exact pow_le_pow_left₀ (norm_nonneg _) hx 2
  have hpoint : ∀ᵐ x ∂μ, Tendsto (fun i => (F i x) ^ 2) l (𝓝 (0 : ℝ)) := by
    filter_upwards [hlim] with x hx
    simpa only [zero_pow (show (2 : ℕ) ≠ 0 by decide)] using hx.pow 2
  have h := tendsto_integral_filter_of_dominated_convergence
    (μ := μ) (F := fun i x => (F i x) ^ 2) (f := fun _ => (0 : ℝ))
    (fun x => g x ^ 2) (Eventually.of_forall fun i => (hF i).pow 2) hbound hg hpoint
  simpa only [integral_zero] using h

/-- Almost-everywhere convergence to zero under an L² bound gives convergence of the L² classes. -/
theorem tendsto_toLp_two_zero_of_dominated {α ι : Type*} [MeasurableSpace α]
    {μ : Measure α} {l : Filter ι} [l.IsCountablyGenerated]
    (F : ι → α → ℝ) (hF : ∀ i, MemLp (F i) 2 μ)
    {g : α → ℝ} (hg : MemLp g 2 μ)
    (hb : ∀ᶠ i in l, ∀ᵐ x ∂μ, ‖F i x‖ ≤ g x)
    (hlim : ∀ᵐ x ∂μ, Tendsto (fun i => F i x) l (𝓝 0)) :
    Tendsto (fun i => (hF i).toLp (F i)) l (𝓝 0) := by
  have hsq := tendsto_integral_sq_zero_of_dominated F
    (fun i => (hF i).aestronglyMeasurable) hg.integrable_sq hb hlim
  apply tendsto_zero_iff_norm_tendsto_zero.mpr
  simpa only [norm_toLp_two_eq_sqrt_integral_sq, Real.sqrt_zero] using hsq.sqrt

end HeatKernel

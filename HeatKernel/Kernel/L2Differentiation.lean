-- Copyright (c) 2026 Scott Armstrong and Amélie Loher. All rights reserved.
-- Released under Apache 2.0 license as described in the file LICENSE.
module

public import HeatKernel.Kernel.L2DominatedConvergence
public import Mathlib.Analysis.Calculus.Deriv.Slope

/-! # Differentiation of scalar L² classes

An L² bound on the errors of scalar difference quotients promotes
almost-everywhere scalar differentiation to differentiation in L².
-/

@[expose] public section

noncomputable section

open MeasureTheory Filter
open scoped Topology

namespace HeatKernel

/-- Dominated scalar difference quotients differentiate the associated L² curve. -/
theorem hasDerivAt_toLp_two_of_dominated_slopes {α : Type*} [MeasurableSpace α]
    {μ : Measure α} (f : ℝ → α → ℝ) (hf : ∀ t, MemLp (f t) 2 μ)
    {a : ℝ} {d g : α → ℝ} (hd : MemLp d 2 μ) (hg : MemLp g 2 μ)
    (hderiv : ∀ᵐ x ∂μ, HasDerivAt (fun t => f t x) (d x) a)
    (hb : ∀ᶠ t in 𝓝[≠] a, ∀ᵐ x ∂μ,
      ‖(t - a)⁻¹ * (f t x - f a x) - d x‖ ≤ g x) :
    HasDerivAt (fun t => (hf t).toLp (f t)) (hd.toLp d) a := by
  let R : ℝ → α → ℝ := fun t x => (t - a)⁻¹ * (f t x - f a x) - d x
  have hR (t : ℝ) : MemLp (R t) 2 μ :=
    (((hf t).sub (hf a)).const_smul ((t - a)⁻¹)).sub hd
  have hpoint : ∀ᵐ x ∂μ, Tendsto (fun t => R t x) (𝓝[≠] a) (𝓝 0) := by
    filter_upwards [hderiv] with x hx
    simpa only [R, slope, vsub_eq_sub, smul_eq_mul, sub_self] using
      hx.tendsto_slope.sub (tendsto_const_nhds (x := d x))
  have hlim := tendsto_toLp_two_zero_of_dominated R hR hg hb hpoint
  have heq (t : ℝ) : (hR t).toLp (R t) =
      slope (fun s => (hf s).toLp (f s)) a t - hd.toLp d := by
    change ((((hf t).sub (hf a)).const_smul ((t - a)⁻¹)).sub hd).toLp
      (((t - a)⁻¹ : ℝ) • (f t - f a) - d) = _
    rfl
  have herr : Tendsto
      (fun t => slope (fun s => (hf s).toLp (f s)) a t - hd.toLp d)
      (𝓝[≠] a) (𝓝 0) := hlim.congr' (Eventually.of_forall heq)
  apply hasDerivAt_iff_tendsto_slope.mpr
  simpa only [sub_add_cancel, zero_add] using
    herr.add (tendsto_const_nhds (x := hd.toLp d))

end HeatKernel

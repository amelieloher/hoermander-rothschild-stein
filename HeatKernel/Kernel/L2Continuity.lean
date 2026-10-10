-- Copyright (c) 2026 Scott Armstrong and Amélie Loher. All rights reserved.
-- Released under Apache 2.0 license as described in the file LICENSE.
module

public import HeatKernel.Kernel.L2DominatedConvergence

/-! # Continuity of scalar L² families

Pointwise convergence with a square-integrable bound on the errors gives
convergence of scalar L² classes to an arbitrary L² limit.
-/

@[expose] public section

noncomputable section

open MeasureTheory Filter
open scoped Topology

namespace HeatKernel

/-- Dominated pointwise convergence gives convergence to the corresponding scalar L² class. -/
theorem tendsto_toLp_two_of_dominated_errors {α ι : Type*} [MeasurableSpace α]
    {μ : Measure α} {l : Filter ι} [l.IsCountablyGenerated]
    (F : ι → α → ℝ) (hF : ∀ i, MemLp (F i) 2 μ)
    {f g : α → ℝ} (hf : MemLp f 2 μ) (hg : MemLp g 2 μ)
    (hb : ∀ᶠ i in l, ∀ᵐ x ∂μ, ‖F i x - f x‖ ≤ g x)
    (hlim : ∀ᵐ x ∂μ, Tendsto (fun i => F i x) l (𝓝 (f x))) :
    Tendsto (fun i => (hF i).toLp (F i)) l (𝓝 (hf.toLp f)) := by
  have hpoint : ∀ᵐ x ∂μ, Tendsto (fun i => F i x - f x) l (𝓝 0) := by
    filter_upwards [hlim] with x hx
    simpa only [sub_self] using hx.sub (tendsto_const_nhds (x := f x))
  have herr := tendsto_toLp_two_zero_of_dominated (fun i x => F i x - f x)
    (fun i => (hF i).sub hf) hg hb hpoint
  have heq (i : ι) : ((hF i).sub hf).toLp (fun x => F i x - f x) =
      (hF i).toLp (F i) - hf.toLp f := rfl
  have hsub : Tendsto (fun i => (hF i).toLp (F i) - hf.toLp f) l (𝓝 0) :=
    herr.congr' (Eventually.of_forall heq)
  simpa only [sub_add_cancel, zero_add] using
    hsub.add (tendsto_const_nhds (x := hf.toLp f))

end HeatKernel

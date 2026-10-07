-- Copyright (c) 2026 Scott Armstrong and Amélie Loher. All rights reserved.
-- Released under Apache 2.0 license as described in the file LICENSE.
module

public import RothschildStein.H3.IntrinsicCurveDerivative
public import Mathlib.Analysis.Calculus.UniformLimitsDeriv
public import Mathlib.Topology.UniformSpace.UniformApproximation

set_option autoImplicit false
set_option relaxedAutoImplicit false
@[expose] public section
noncomputable section
open Set Filter Metric TopologicalSpace
open scoped Topology
namespace RothschildStein.H3
variable {N : ℕ}

/-- Uniform convergence of continuous scalar inputs and their
continuous fixed intrinsic derivatives preserves the intrinsic derivative
at every point. The proof tests every local integral curve and uses the
uniform derivative limit theorem on an actual open time interval
(BB proof of Proposition 3.48(ii)). -/
theorem hasIntrinsicDeriv_of_uniform_limits
    (Ω : Opens (Fin N → ℝ)) (X : (Fin N → ℝ) → (Fin N → ℝ))
    (f g : ℕ → (Fin N → ℝ) → ℝ) (u v : (Fin N → ℝ) → ℝ)
    (hf : ∀ n, hasIntrinsicDeriv Ω X (f n) (g n))
    (hc : ∀ n, ContinuousOn (f n) (Ω : Set (Fin N → ℝ)))
    (hgc : ∀ n, ContinuousOn (g n) (Ω : Set (Fin N → ℝ)))
    (hu : TendstoUniformlyOn f u atTop (Ω : Set (Fin N → ℝ)))
    (hv : TendstoUniformlyOn g v atTop (Ω : Set (Fin N → ℝ))) :
    ContinuousOn u (Ω : Set (Fin N → ℝ)) ∧
    ContinuousOn v (Ω : Set (Fin N → ℝ)) ∧ hasIntrinsicDeriv Ω X u v := by
  refine ⟨hu.continuousOn (Frequently.of_forall hc),
    hv.continuousOn (Frequently.of_forall hgc), ?_⟩
  intro x hx
  refine ⟨(hf 0 x hx).1, ?_⟩
  intro γ hzero hγ hmem
  obtain ⟨ε, hε, hball⟩ := Metric.eventually_nhds_iff_ball.mp (hγ.and hmem)
  let I : Set ℝ := ball 0 ε
  have hI : IsOpen I := isOpen_ball
  have hI0 : (0 : ℝ) ∈ I := mem_ball_self hε
  have hγI (t : ℝ) (ht : t ∈ I) : IsIntegralCurveAt γ (fun _ => X) t := by
    filter_upwards [hI.mem_nhds ht] with s hs
    exact (hball s hs).1
  have hmaps : MapsTo γ I (Ω : Set (Fin N → ℝ)) := fun t ht => (hball t ht).2
  have hd (n : ℕ) (t : ℝ) (ht : t ∈ I) :
      HasDerivAt (f n ∘ γ) (g n (γ t)) t :=
    hasDerivAt_comp_curve_of_intrinsic Ω X (hf n) (hγI t ht)
      (Eventually.mono (hI.mem_nhds ht) hmaps)
  have H := hasDerivAt_of_tendstoUniformlyOn hI ((hv.comp γ).mono hmaps)
    (Eventually.of_forall hd)
    (fun t ht => hu.tendsto_at (hmaps ht)) hI0
  simpa only [Function.comp_apply, hzero] using H

end RothschildStein.H3

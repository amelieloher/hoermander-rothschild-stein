-- Copyright (c) 2026 Scott Armstrong and Amélie Loher. All rights reserved.
-- Released under Apache 2.0 license as described in the file LICENSE.
module

public import RothschildStein.Definitions.hasIntrinsicWordDeriv
public import Mathlib.Analysis.Calculus.MeanValue

set_option autoImplicit false
set_option relaxedAutoImplicit false
set_option backward.isDefEq.respectTransparency false
@[expose] public section
noncomputable section
open Set Filter TopologicalSpace Metric
open scoped Topology
namespace RothschildStein.P1

/-- Any function, without a continuity premise, has zero
intrinsic derivative along the zero field: every local integral curve
is locally constant, by the mean value theorem. -/
theorem hasIntrinsicDeriv_zero_field {n : ℕ}
    (Ω : Opens (Fin n → ℝ)) (f : (Fin n → ℝ) → ℝ) :
    hasIntrinsicDeriv Ω (fun _ => 0) f (fun _ => 0) := by
  intro x hx
  refine ⟨⟨fun _ => x, rfl, ?_, ?_⟩, ?_⟩
  · exact Eventually.of_forall fun t => hasDerivAt_const t x
  · exact Eventually.of_forall fun _ => hx
  · intro γ hγ0 hγ _
    obtain ⟨r, hr, hball⟩ := Metric.eventually_nhds_iff.mp hγ
    have he : (fun t => f (γ t)) =ᶠ[𝓝 (0 : ℝ)] fun _ => f x := by
      filter_upwards [Metric.ball_mem_nhds (0 : ℝ) hr] with t ht
      have ht0 : (0 : ℝ) ∈ Metric.ball 0 r := Metric.mem_ball_self hr
      have hc : γ t = γ 0 := isOpen_ball.is_const_of_deriv_eq_zero
        (convex_ball (0 : ℝ) r).isPreconnected
        (fun y hy => (hball (by simpa only [Metric.mem_ball] using hy)).differentiableAt.differentiableWithinAt)
        (fun y hy => (hball (by simpa only [Metric.mem_ball] using hy)).deriv) ht ht0
      rw [hc, hγ0]
    exact (hasDerivAt_const (0 : ℝ) (f x)).congr_of_eventuallyEq he

end RothschildStein.P1

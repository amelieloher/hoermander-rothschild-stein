-- Copyright (c) 2026 Scott Armstrong and Amélie Loher. All rights reserved.
-- Released under Apache 2.0 license as described in the file LICENSE.
module

public import HeatKernel.Form.WeakCompactness
public import Mathlib.Analysis.InnerProductSpace.Adjoint

/-!
# Lifting strong limits through a Hilbert inclusion

A bounded sequence in a separable Hilbert space has a weak limit above any strong limit of
its image under a bounded linear map. A uniform norm bound on a second linear image survives.
-/

@[expose] public section

noncomputable section

open Set Filter TopologicalSpace
open scoped Topology

namespace HeatKernel

/-- Strong limits of the first image of a bounded Hilbert sequence have lifts preserving a
uniform norm bound on a second image. -/
theorem exists_lift_of_tendsto_of_bounded {E H K : Type*}
    [NormedAddCommGroup E] [InnerProductSpace ℝ E] [CompleteSpace E] [SeparableSpace E]
    [NormedAddCommGroup H] [InnerProductSpace ℝ H] [CompleteSpace H]
    [NormedAddCommGroup K] [NormedSpace ℝ K]
    (A : E →L[ℝ] H) (B : E →L[ℝ] K) (u : ℕ → E) {h : H} {M C : ℝ}
    (hu : ∀ n, ‖u n‖ ≤ M) (hB : ∀ n, ‖B (u n)‖ ≤ C)
    (ht : Tendsto (fun n => A (u n)) atTop (𝓝 h)) :
    ∃ z : E, A z = h ∧ ‖z‖ ≤ M ∧ ‖B z‖ ≤ C := by
  obtain ⟨z, hz, ns, hns, hweak⟩ := exists_weakly_convergent_subseq u hu
  have heq : A z = h := by
    apply ext_inner_left ℝ
    intro y
    have H := (tendsto_weak_iff_inner.mp hweak) (A.adjoint y)
    simp only [ContinuousLinearMap.adjoint_inner_left] at H
    have H' : Tendsto (fun n => inner ℝ y (A (u (ns n)))) atTop (𝓝 (inner ℝ y h)) :=
      (continuous_const.inner continuous_id).continuousAt.tendsto.comp
        (ht.comp hns.tendsto_atTop)
    exact tendsto_nhds_unique H H' 
  have hconv : Convex ℝ (B ⁻¹' Metric.closedBall (0 : K) C) :=
    (convex_closedBall (0 : K) C).linear_preimage B.toLinearMap
  have hclosed : IsClosed (B ⁻¹' Metric.closedBall (0 : K) C) :=
    Metric.isClosed_closedBall.preimage B.continuous
  have hmem := mem_of_tendsto_weak_of_convex hconv hclosed
    (fun n => (by simpa only [mem_preimage, Metric.mem_closedBall, dist_zero_right] using hB (ns n)))
    hweak
  exact ⟨z, heq, hz, by simpa only [mem_preimage, Metric.mem_closedBall, dist_zero_right] using hmem⟩

end HeatKernel

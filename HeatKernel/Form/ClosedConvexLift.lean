-- Copyright (c) 2026 Scott Armstrong and Amélie Loher. All rights reserved.
-- Released under Apache 2.0 license as described in the file LICENSE.
module

public import HeatKernel.Form.WeakLift
import Mathlib.Tactic.Linter

/-! # Strong image limits with closed convex constraints -/

@[expose] public section

noncomputable section

open Set Filter TopologicalSpace
open scoped Topology

namespace HeatKernel

/-- A strongly converging image of a bounded Hilbert sequence has a lift in any norm-closed
convex set containing that sequence. -/
theorem exists_lift_of_tendsto_of_bounded_mem_closed_convex {E H : Type*}
    [NormedAddCommGroup E] [InnerProductSpace ℝ E] [CompleteSpace E] [SeparableSpace E]
    [NormedAddCommGroup H] [InnerProductSpace ℝ H] [CompleteSpace H]
    (A : E →L[ℝ] H) (u : ℕ → E) {h : H} {M : ℝ} {C : Set E}
    (hu : ∀ n, ‖u n‖ ≤ M) (hC : Convex ℝ C) (hc : IsClosed C)
    (hmem : ∀ n, u n ∈ C) (ht : Tendsto (fun n => A (u n)) atTop (𝓝 h)) :
    ∃ z : E, A z = h ∧ ‖z‖ ≤ M ∧ z ∈ C := by
  obtain ⟨z, hz, ns, hns, hweak⟩ := exists_weakly_convergent_subseq u hu
  have heq : A z = h := by
    apply ext_inner_left ℝ
    intro y
    have H := (tendsto_weak_iff_inner.mp hweak) (A.adjoint y)
    simp only [ContinuousLinearMap.adjoint_inner_left] at H
    have H' : Tendsto (fun n => inner ℝ y (A (u (ns n)))) atTop (𝓝 (inner ℝ y h)) :=
      (continuous_const.inner continuous_id).continuousAt.tendsto.comp (ht.comp hns.tendsto_atTop)
    exact tendsto_nhds_unique H H'
  exact ⟨z, heq, hz, mem_of_tendsto_weak_of_convex hC hc (fun n => hmem (ns n)) hweak⟩


end HeatKernel

-- Copyright (c) 2026 Scott Armstrong and Amélie Loher. All rights reserved.
-- Released under Apache 2.0 license as described in the file LICENSE.
module

public import Mathlib.Analysis.InnerProductSpace.Dual
public import Mathlib.Analysis.Normed.Module.WeakDual
public import Mathlib.Analysis.LocallyConvex.WeakSpace
public import Mathlib.Topology.Semicontinuity.Basic

/-!
# Weak compactness in real Hilbert spaces

Bounded sequences in a separable real Hilbert space have weakly convergent subsequences.
Closed convex sets remain closed in the weak topology, and the norm is weakly lower
semicontinuous. These results apply to both an energy space and its gradient space.
-/

@[expose] public section

noncomputable section

open Set Filter TopologicalSpace
open scoped Topology

namespace HeatKernel

section NormedSpace

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]

/-- A norm-closed convex set is closed for the weak topology. -/
theorem isClosed_toWeakSpace_image_of_convex {s : Set E}
    (hs : Convex ℝ s) (hc : IsClosed s) : IsClosed (toWeakSpace ℝ E '' s) := by
  rw [← closure_eq_iff_isClosed, ← hs.toWeakSpace_closure ℝ, hc.closure_eq]

/-- A weak limit of a sequence in a norm-closed convex set still belongs to the set. -/
theorem mem_of_tendsto_weak_of_convex {s : Set E} (hs : Convex ℝ s) (hc : IsClosed s)
    {u : ℕ → E} {x : E} (hu : ∀ n, u n ∈ s)
    (hlim : Tendsto (fun n => toWeakSpace ℝ E (u n)) atTop
      (𝓝 (toWeakSpace ℝ E x))) : x ∈ s := by
  have hx := (isClosed_toWeakSpace_image_of_convex hs hc).mem_of_tendsto hlim
    (Eventually.of_forall fun n => mem_image_of_mem _ (hu n))
  exact (toWeakSpace ℝ E).injective.mem_set_image.mp hx

end NormedSpace

section HilbertSpace

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [CompleteSpace E]

/-- Weak convergence in a real Hilbert space is convergence of all inner products. -/
theorem tendsto_weak_iff_inner {α : Type*} {l : Filter α} {u : α → E} {x : E} :
    Tendsto (fun n => toWeakSpace ℝ E (u n)) l (𝓝 (toWeakSpace ℝ E x)) ↔
      ∀ y, Tendsto (fun n => inner ℝ y (u n)) l (𝓝 (inner ℝ y x)) := by
  have hinj : Function.Injective (topDualPairing ℝ E).flip := by
    intro x y h
    apply ext_inner_left ℝ
    intro z
    exact congrArg (fun f => f ((InnerProductSpace.toDual ℝ E) z)) h
  exact (WeakBilin.tendsto_iff_forall_eval_tendsto
    (topDualPairing ℝ E).flip hinj).trans
    (by
      constructor
      · intro h y
        exact h ((InnerProductSpace.toDual ℝ E) y)
      · intro h f
        obtain ⟨y, rfl⟩ := (InnerProductSpace.toDual ℝ E).surjective f
        exact h y)

/-- Every norm-bounded sequence in a separable real Hilbert space has a weakly
convergent subsequence, with its limit in the same norm ball. -/
theorem exists_weakly_convergent_subseq [SeparableSpace E]
    (u : ℕ → E) {C : ℝ} (hu : ∀ n, ‖u n‖ ≤ C) :
    ∃ x : E, ‖x‖ ≤ C ∧ ∃ φ : ℕ → ℕ, StrictMono φ ∧
      Tendsto (fun n => toWeakSpace ℝ E (u (φ n))) atTop
        (𝓝 (toWeakSpace ℝ E x)) := by
  let v : ℕ → WeakDual ℝ E := fun n =>
    StrongDual.toWeakDual ((InnerProductSpace.toDual ℝ E) (u n))
  have hv : ∀ n, v n ∈ WeakDual.toStrongDual ⁻¹' Metric.closedBall 0 C := by
    intro n
    simpa [v, Metric.mem_closedBall, dist_zero_right] using hu n
  obtain ⟨f, hf, φ, hφ, hlim⟩ := (WeakDual.isSeqCompact_closedBall ℝ E 0 C) hv
  let x : E := (InnerProductSpace.toDual ℝ E).symm (WeakDual.toStrongDual f)
  refine ⟨x, ?_, φ, hφ, tendsto_weak_iff_inner.mpr ?_⟩
  · simpa [x, Metric.mem_closedBall, dist_zero_right] using hf
  · intro y
    have hy := (WeakDual.eval_continuous y).tendsto f |>.comp hlim
    have hx : inner ℝ y x = f y := by
      rw [real_inner_comm]
      exact InnerProductSpace.toDual_symm_apply
    rw [hx]
    simpa [v, Function.comp_def, real_inner_comm] using hy

end HilbertSpace

end HeatKernel

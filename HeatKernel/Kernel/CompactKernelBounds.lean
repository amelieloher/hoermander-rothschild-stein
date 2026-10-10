-- Copyright (c) 2026 Scott Armstrong and Amélie Loher. All rights reserved.
-- Released under Apache 2.0 license as described in the file LICENSE.
module

public import HeatKernel.Kernel.EvaluationKernel
public import Mathlib.Analysis.Normed.Operator.BanachSteinhaus
public import Mathlib.Analysis.Normed.Group.Bounded

/-! # Compact bounds from scalar continuity of evaluations

Uniform boundedness converts compact scalar bounds into uniform operator bounds.
The Riesz inner-product formula then bounds the kernel on compact sets.
-/

@[expose] public section

noncomputable section

namespace HeatKernel

/-- Scalar continuity bounds a family of bounded functionals uniformly on compact sets. -/
theorem exists_norm_bound_on_compact_of_continuous_apply {P H : Type*}
    [TopologicalSpace P] [NormedAddCommGroup H] [NormedSpace ℝ H] [CompleteSpace H]
    (L : P → H →L[ℝ] ℝ) {K : Set P} (hK : IsCompact K)
    (hL : ∀ f, ContinuousOn (fun p => L p f) K) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ p ∈ K, ‖L p‖ ≤ C := by
  obtain ⟨C, hC⟩ := banach_steinhaus (g := fun p : K => L p) (by
    intro f
    obtain ⟨D, hD⟩ := hK.exists_bound_of_continuousOn (hL f)
    exact ⟨D, fun p => hD p p.property⟩)
  exact ⟨max C 0, le_max_right _ _, fun p hp => (hC ⟨p, hp⟩).trans (le_max_left _ _)⟩

/-- Continuity of scalar evaluations at both half-time endpoints bounds the kernel on a compact set. -/
theorem exists_abs_evaluationKernel_bound_on_compact {H A : Type*}
    [NormedAddCommGroup H] [InnerProductSpace ℝ H] [CompleteSpace H] [TopologicalSpace A]
    (L : ℝ → A → H →L[ℝ] ℝ) {K : Set (ℝ × (A × A))} (hK : IsCompact K)
    (hleft : ∀ f, ContinuousOn (fun p : ℝ × (A × A) => L (p.1 / 2) p.2.1 f) K)
    (hright : ∀ f, ContinuousOn (fun p : ℝ × (A × A) => L (p.1 / 2) p.2.2 f) K) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ p ∈ K, |evaluationKernel L p.1 p.2.1 p.2.2| ≤ C := by
  obtain ⟨C, hC, hleftBound⟩ := exists_norm_bound_on_compact_of_continuous_apply
    (fun p : ℝ × (A × A) => L (p.1 / 2) p.2.1) hK hleft
  obtain ⟨D, hD, hrightBound⟩ := exists_norm_bound_on_compact_of_continuous_apply
    (fun p : ℝ × (A × A) => L (p.1 / 2) p.2.2) hK hright
  exact ⟨C * D, mul_nonneg hC hD, fun p hp =>
    abs_evaluationKernel_le L p.1 p.2.1 p.2.2 (hleftBound p hp) (hrightBound p hp)⟩

end HeatKernel

-- Copyright (c) 2026 Scott Armstrong and Amélie Loher. All rights reserved.
-- Released under Apache 2.0 license as described in the file LICENSE.
module

public import HeatKernel.Form.LocalScalarExtensions
public import Mathlib.Topology.Compactness.Lindelof
import Mathlib.Tactic.Linter

/-! # Countable global smooth branches for locally C¹ scalar maps -/

@[expose] public section

noncomputable section

open Set Filter TopologicalSpace
open scoped NNReal Topology

namespace HeatKernel

/-- A scalar map that is locally C¹ outside a set has a countable family of global compactly
supported C¹ branches with bounded derivatives covering its values and derivatives there. -/
theorem exists_countable_contDiff_scalar_branches {η : ℝ → ℝ} (S : Set ℝ)
    (hη : ∀ s ∉ S, ContDiffAt ℝ 1 η s) :
    ∃ B : Set ((ℝ → ℝ) × ℝ≥0), B.Countable ∧
      (∀ b ∈ B, ContDiff ℝ 1 b.1 ∧ HasCompactSupport b.1 ∧ ∀ s, ‖deriv b.1 s‖ ≤ b.2) ∧
      ∀ s ∉ S, ∃ b ∈ B, η s = b.1 s ∧ deriv η s = deriv b.1 s := by
  classical
  have hlocal : ∀ a : {s : ℝ // s ∉ S}, ∃ ψ : ℝ → ℝ, ∃ C : ℝ≥0,
      ContDiff ℝ 1 ψ ∧ HasCompactSupport ψ ∧ (∀ s, ‖deriv ψ s‖ ≤ C) ∧ ψ =ᶠ[𝓝 (a : ℝ)] η :=
    fun a => exists_contDiff_compactSupport_extension_at (hη a a.property)
  choose ψ C hψ hc hb he using hlocal
  have hnear : ∀ a : {s : ℝ // s ∉ S}, ∃ V : Set ℝ,
      (∀ s ∈ V, η s = ψ a s ∧ deriv η s = deriv (ψ a) s) ∧ IsOpen V ∧ (a : ℝ) ∈ V :=
    fun a => eventually_nhds_iff.mp ((he a).symm.and (he a).deriv.symm)
  choose V hmatch hopen hpoint using hnear
  have hcover : Sᶜ ⊆ ⋃ a : {s : ℝ // s ∉ S}, V a := by
    intro s hs
    exact mem_iUnion.mpr ⟨⟨s, hs⟩, hpoint ⟨s, hs⟩⟩
  obtain ⟨R, hR, hRc⟩ := (HereditarilyLindelofSpace.isLindelof Sᶜ).elim_countable_subcover V hopen hcover
  let f : {s : ℝ // s ∉ S} → (ℝ → ℝ) × ℝ≥0 := fun a => (ψ a, C a)
  refine ⟨f '' R, hR.image f, ?_, ?_⟩
  · rintro b ⟨a, _, rfl⟩
    exact ⟨hψ a, hc a, hb a⟩
  · intro s hs
    obtain ⟨a, ha⟩ := mem_iUnion.mp (hRc hs)
    obtain ⟨har, has⟩ := mem_iUnion.mp ha
    exact ⟨f a, mem_image_of_mem f har, hmatch a s has⟩



end HeatKernel

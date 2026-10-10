-- Copyright (c) 2026 Scott Armstrong and Amélie Loher. All rights reserved.
-- Released under Apache 2.0 license as described in the file LICENSE.
module

public import HeatKernel.Form.CountableScalarBranches
public import HeatKernel.Form.CountableBranchChainRule
import Mathlib.Tactic.Linter

/-! # Horizontal chain rules for scalar maps with countably many exceptional levels -/

@[expose] public section

noncomputable section

open Set MeasureTheory Filter TopologicalSpace
open scoped NNReal Topology

namespace HeatKernel

/-- An energy representative of a scalar composition obeys the exact chain rule if the scalar
map is locally C¹ off countably many levels. The derivative value on those levels is arbitrary. -/
theorem energyGraph_chainRule_contDiffAt_off_countable {N q : ℕ}
    (X : Fin q → (Fin N → ℝ) → (Fin N → ℝ))
    (hX : ∀ i, ContDiff ℝ (⊤ : ℕ∞) (X i))
    (u w : energyGraph (N := N) ⊤ X) {η d : ℝ → ℝ}
    (hw : (w : GradientSpace (N := N) ⊤ q).fst =ᵐ[volume]
      fun x => η ((u : GradientSpace (N := N) ⊤ q).fst x))
    (S : Set ℝ) (hS : S.Countable) (hη : ∀ s ∉ S, ContDiffAt ℝ 1 η s)
    (hd : ∀ s ∉ S, d s = deriv η s) (i : Fin q) :
    (w : GradientSpace (N := N) ⊤ q).snd i =ᵐ[volume]
      fun x => d ((u : GradientSpace (N := N) ⊤ q).fst x) *
        (u : GradientSpace (N := N) ⊤ q).snd i x := by
  obtain ⟨B, hB, hb, hcover⟩ := exists_countable_contDiff_scalar_branches S hη
  have : Countable B := hB.to_subtype
  apply energyGraph_chainRule_of_countable_smooth_branches (A := B) X hX u w hw S hS
    (fun b => b.val.1) (fun b => (hb b b.property).1) (fun b => b.val.2)
    (fun b => (hb b b.property).2.2)
  intro s hs
  obtain ⟨b, hbin, he, he'⟩ := hcover s hs
  exact ⟨⟨b, hbin⟩, he, (hd s hs).trans he'⟩

/-- A Lipschitz scalar map fixing zero and locally C¹ off countably many levels preserves the
energy graph, with the exact spatial chain rule and the Lipschitz graph-norm bound. -/
theorem exists_energyGraph_comp_contDiffAt_off_countable {N q : ℕ}
    (X : Fin q → (Fin N → ℝ) → (Fin N → ℝ))
    (hX : ∀ i, ContDiff ℝ (⊤ : ℕ∞) (X i)) (u : energyGraph (N := N) ⊤ X)
    {η d : ℝ → ℝ} {L : ℝ≥0} (hLip : LipschitzWith L η) (hzero : η 0 = 0)
    (S : Set ℝ) (hS : S.Countable) (hη : ∀ s ∉ S, ContDiffAt ℝ 1 η s)
    (hd : ∀ s ∉ S, d s = deriv η s) :
    ∃ w : energyGraph (N := N) ⊤ X,
      (w : GradientSpace (N := N) ⊤ q).fst =ᵐ[volume]
        (fun x => η ((u : GradientSpace (N := N) ⊤ q).fst x)) ∧
      (∀ i, (w : GradientSpace (N := N) ⊤ q).snd i =ᵐ[volume]
        fun x => d ((u : GradientSpace (N := N) ⊤ q).fst x) *
          (u : GradientSpace (N := N) ⊤ q).snd i x) ∧ ‖w‖ ≤ (L : ℝ) * ‖u‖ := by
  obtain ⟨w, hw, hn⟩ := exists_energyGraph_comp_lipschitz_norm_le X hX u hLip hzero
  exact ⟨w, hw, fun i => energyGraph_chainRule_contDiffAt_off_countable X hX u w hw
    S hS hη hd i, hn⟩



end HeatKernel

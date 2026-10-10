-- Copyright (c) 2026 Scott Armstrong and Amélie Loher. All rights reserved.
-- Released under Apache 2.0 license as described in the file LICENSE.
module

public import HeatKernel.Form.SmoothBranchGradients
public import HeatKernel.Form.CountableLevelGradients
public import HeatKernel.Form.LipschitzGraphBounds
import Mathlib.Tactic.Linter

/-! # Horizontal chain rules from countable smooth branch covers -/

@[expose] public section

noncomputable section

open Set MeasureTheory Filter TopologicalSpace
open scoped NNReal

namespace HeatKernel

/-- Countably many smooth scalar branches determine the horizontal chain rule off a countable
exceptional set of levels. The derivative may be assigned arbitrarily on the exceptional set. -/
theorem energyGraph_chainRule_of_countable_smooth_branches {N q : ℕ} {A : Type*} [Countable A]
    (X : Fin q → (Fin N → ℝ) → (Fin N → ℝ))
    (hX : ∀ i, ContDiff ℝ (⊤ : ℕ∞) (X i))
    (u w : energyGraph (N := N) ⊤ X) {η d : ℝ → ℝ}
    (hw : (w : GradientSpace (N := N) ⊤ q).fst =ᵐ[volume]
      fun x => η ((u : GradientSpace (N := N) ⊤ q).fst x))
    (S : Set ℝ) (hS : S.Countable) (ψ : A → ℝ → ℝ)
    (hψ : ∀ a, ContDiff ℝ 1 (ψ a)) (C : A → ℝ≥0)
    (hb : ∀ a s, ‖deriv (ψ a) s‖ ≤ C a)
    (hcover : ∀ s ∉ S, ∃ a, η s = ψ a s ∧ d s = deriv (ψ a) s) (i : Fin q) :
    (w : GradientSpace (N := N) ⊤ q).snd i =ᵐ[volume]
      fun x => d ((u : GradientSpace (N := N) ⊤ q).fst x) *
        (u : GradientSpace (N := N) ⊤ q).snd i x := by
  have hbranch := fun a => energyGraph_gradient_eq_on_smooth_branch X hX u w hw (hψ a) (hb a) i
  filter_upwards [hw, ae_all_iff.mpr hbranch,
    energyGraph_gradient_zero_on_countable_levels X hX u S hS i,
    energyGraph_gradient_zero_on_countable_levels X hX w (η '' S) (hS.image η) i]
    with x hwx hx huz hwz
  by_cases hs : (u : GradientSpace (N := N) ⊤ q).fst x ∈ S
  · have hw0 : (w : GradientSpace (N := N) ⊤ q).snd i x = 0 :=
      hwz (hwx ▸ mem_image_of_mem η hs)
    rw [hw0, huz hs, mul_zero]
  · obtain ⟨a, ha, hd⟩ := hcover _ hs
    rw [hx a ha, hd]

end HeatKernel

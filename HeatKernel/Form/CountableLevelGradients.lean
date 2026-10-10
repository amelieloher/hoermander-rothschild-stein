-- Copyright (c) 2026 Scott Armstrong and Amélie Loher. All rights reserved.
-- Released under Apache 2.0 license as described in the file LICENSE.
module

public import HeatKernel.Form.LevelSetGradient
import Mathlib.Tactic.Linter

/-! # Horizontal gradients vanish on countably many scalar levels -/

@[expose] public section

noncomputable section

open Set MeasureTheory Filter TopologicalSpace

namespace HeatKernel

/-- The horizontal gradient vanishes almost everywhere on the inverse image of any countable
set of scalar levels, with one common exceptional null set. -/
theorem energyGraph_gradient_zero_on_countable_levels {N q : ℕ}
    (X : Fin q → (Fin N → ℝ) → (Fin N → ℝ))
    (hX : ∀ i, ContDiff ℝ (⊤ : ℕ∞) (X i)) (u : energyGraph (N := N) ⊤ X)
    (S : Set ℝ) (hS : S.Countable) (i : Fin q) :
    ∀ᵐ x ∂volume, (u : GradientSpace (N := N) ⊤ q).fst x ∈ S →
      (u : GradientSpace (N := N) ⊤ q).snd i x = 0 := by
  have : Countable S := hS.to_subtype
  have h : ∀ c : S, ∀ᵐ x ∂volume, (u : GradientSpace (N := N) ⊤ q).fst x = (c : ℝ) →
      (u : GradientSpace (N := N) ⊤ q).snd i x = 0 := fun c =>
    energyGraph_gradient_zero_on_level X hX u c i
  filter_upwards [ae_all_iff.mpr h] with x hx hs
  exact hx ⟨_, hs⟩ rfl



end HeatKernel

-- Copyright (c) 2026 Scott Armstrong and Amélie Loher. All rights reserved.
-- Released under Apache 2.0 license as described in the file LICENSE.
module

public import RothschildStein.S.Sobolev
public import RothschildStein.S.HolderBounds
public import RothschildStein.Definitions.holderENorm

set_option autoImplicit false
set_option relaxedAutoImplicit false
@[expose] public section
noncomputable section
open Set TopologicalSpace
open scoped ENNReal
namespace RothschildStein.S
variable {n q : ℕ}

/-- The weak Hölder class has a finite empty-word norm and weak representatives for the entire weighted family (BB Definition 2.13, p. 81). -/
def memWeakHolderX (w : Fin q → ℕ+)
    (X : Fin q → (Fin n → ℝ) → (Fin n → ℝ))
    (d : (Fin n → ℝ) → (Fin n → ℝ) → ℝ≥0∞)
    (Ω : Opens (Fin n → ℝ)) (k : ℕ) (α : ℝ) (f : (Fin n → ℝ) → ℝ) : Prop :=
  holderENorm d α (Ω : Set (Fin n → ℝ)) f < ⊤ ∧
    ∀ I ∈ wordFamily w k, ∃ g : (Fin n → ℝ) → ℝ,
      hasWeakWordDeriv X Ω I f g ∧ holderENorm d α (Ω : Set (Fin n → ℝ)) g < ⊤

/-- Restricting a weak Hölder class preserves the weighted
word data and its pointwise empty-word condition (BB Prop 2.18, p. 84). -/
theorem memWeakHolderX_restrict
    (w : Fin q → ℕ+) (X : Fin q → (Fin n → ℝ) → (Fin n → ℝ))
    (d : (Fin n → ℝ) → (Fin n → ℝ) → ℝ≥0∞)
    (Ω U : Opens (Fin n → ℝ)) (hU : (U : Set (Fin n → ℝ)) ⊆ Ω)
    (k : ℕ) (α : ℝ) {f : (Fin n → ℝ) → ℝ}
    (hf : memWeakHolderX w X d Ω k α f) : memWeakHolderX w X d U k α f := by
  refine ⟨?_,fun I hI => ?_⟩
  · exact lt_of_le_of_lt (holderENorm_mono d α (Ω : Set (Fin n → ℝ)) f hU) hf.1
  · obtain ⟨g,hg,hn⟩ := hf.2 I hI
    exact ⟨g,hasWeakWordDeriv_restrict X Ω U hU hg,
      lt_of_le_of_lt (holderENorm_mono d α (Ω : Set (Fin n → ℝ)) g hU) hn⟩

end RothschildStein.S

-- Copyright (c) 2026 Scott Armstrong and Amélie Loher. All rights reserved.
-- Released under Apache 2.0 license as described in the file LICENSE.
module

public import RothschildStein.Definitions.memHolderX

set_option autoImplicit false
set_option relaxedAutoImplicit false
@[expose] public section
noncomputable section
open Set TopologicalSpace
open scoped ENNReal
namespace RothschildStein.S
variable {n q : ℕ}

/-- The Hölder class supplies one
normalized family of intrinsic word representatives, with its empty
word exactly equal to the input (BB Def 2.13, pp. 81–82). -/
theorem exists_intrinsicHolder_representatives
    (w : Fin q → ℕ+) (X : Fin q → (Fin n → ℝ) → (Fin n → ℝ))
    (d : (Fin n → ℝ) → (Fin n → ℝ) → ℝ≥0∞)
    (Ω : Opens (Fin n → ℝ)) (k : ℕ) (α : ℝ) {f : (Fin n → ℝ) → ℝ}
    (hf : memHolderX w X d Ω k α f) :
    ∃ jet : List (Fin q) → (Fin n → ℝ) → ℝ,
      jet [] = f ∧ ∀ I ∈ wordFamily w k,
        hasIntrinsicWordDeriv X Ω I f (jet I) ∧
          holderENorm d α (Ω : Set (Fin n → ℝ)) (jet I) < ⊤ := by
  classical
  let jet := fun I : List (Fin q) => if I = [] then f else
    if hI : I ∈ wordFamily w k then (hf.2 I hI).choose else (fun _ => (0 : ℝ))
  refine ⟨jet,by simp [jet],?_⟩
  intro I hI
  by_cases hn : I = []
  · subst I
    simp only [jet,ite_eq_left rfl]
    exact ⟨fun _ _ => rfl,hf.1⟩
  · simp only [jet,ite_eq_right hn,dite_eq_left hI]
    exact (hf.2 I hI).choose_spec

end RothschildStein.S

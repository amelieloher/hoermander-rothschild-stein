-- Copyright (c) 2026 Scott Armstrong and Amélie Loher. All rights reserved.
-- Released under Apache 2.0 license as described in the file LICENSE.
module

public import RothschildStein.S.WeakHolderSpaces

set_option autoImplicit false
set_option relaxedAutoImplicit false
@[expose] public section
noncomputable section
open Set MeasureTheory TopologicalSpace
open scoped ENNReal
namespace RothschildStein.S
variable {n q : ℕ}

/-- One family of weak Hölder representatives can be chosen
with the empty word exactly the original pointwise input (BB Def 2.13,
p. 81; normalized weak-carrier). -/
theorem exists_weakHolder_representatives
    (w : Fin q → ℕ+) (X : Fin q → (Fin n → ℝ) → (Fin n → ℝ))
    (d : (Fin n → ℝ) → (Fin n → ℝ) → ℝ≥0∞)
    (Ω : Opens (Fin n → ℝ)) (k : ℕ) (α : ℝ) {f : (Fin n → ℝ) → ℝ}
    (hf : memWeakHolderX w X d Ω k α f) :
    ∃ jet : List (Fin q) → (Fin n → ℝ) → ℝ,
      jet [] = f ∧ ∀ I ∈ wordFamily w k,
        hasWeakWordDeriv X Ω I f (jet I) ∧ holderENorm d α (Ω : Set (Fin n → ℝ)) (jet I) < ⊤ := by
  classical
  let jet := fun I : List (Fin q) => if I = [] then f else
    if hI : I ∈ wordFamily w k then (hf.2 I hI).choose else (fun _ => (0 : ℝ))
  refine ⟨jet,by simp [jet],?_⟩
  intro I hI
  by_cases hn : I = []
  · subst I
    simp only [jet,ite_eq_left rfl]
    exact ⟨hasWeakWordDeriv_nil X Ω ((hf.2 [] (nil_mem_wordFamily w k)).choose_spec.1.1),hf.1⟩
  · simp only [jet,ite_eq_right hn,dite_eq_left hI]
    exact (hf.2 I hI).choose_spec

end RothschildStein.S

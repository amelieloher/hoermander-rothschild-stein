-- Copyright (c) 2026 Scott Armstrong and Amélie Loher. All rights reserved.
-- Released under Apache 2.0 license as described in the file LICENSE.
module

public import RothschildStein.S.Sobolev

set_option autoImplicit false
set_option relaxedAutoImplicit false
@[expose] public section
noncomputable section
open Set MeasureTheory TopologicalSpace
open scoped ENNReal
namespace RothschildStein.S
variable {n q : ℕ} {p : ℝ≥0∞} [Fact (1 ≤ p)]

/-- Sobolev membership supplies one family of weak Lp word
representatives with the empty word fixed to the original representative
(BB Def. 2.2, p. 68; finite-family). -/
theorem exists_sobolev_representatives
    (w : Fin q → ℕ+) (X : Fin q → (Fin n → ℝ) → (Fin n → ℝ))
    (Ω : Opens (Fin n → ℝ)) (k : ℕ) {f : (Fin n → ℝ) → ℝ}
    (hf : memSobolevX w X Ω k p f) :
    ∃ jet : List (Fin q) → (Fin n → ℝ) → ℝ,
      jet [] = f ∧ ∀ I ∈ wordFamily w k,
        hasWeakWordDeriv X Ω I f (jet I) ∧
        MemLp (jet I) p (volume.restrict (Ω : Set (Fin n → ℝ))) := by
  classical
  let jet := fun I : List (Fin q) => if I = [] then f else
    if hI : I ∈ wordFamily w k then (hf.2 I hI).choose else (fun _ => (0 : ℝ))
  refine ⟨jet,by simp [jet],?_⟩
  intro I hI
  by_cases hn : I = []
  · subst I
    simp only [jet,ite_eq_left rfl]
    exact ⟨hasWeakWordDeriv_nil X Ω
      (locallyIntegrableOn_of_locallyIntegrable_restrict (hf.1.locallyIntegrable Fact.out)),hf.1⟩
  · simp only [jet,ite_eq_right hn,dite_eq_left hI]
    exact (hf.2 I hI).choose_spec

end RothschildStein.S

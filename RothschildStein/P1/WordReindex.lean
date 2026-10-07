-- Copyright (c) 2026 Scott Armstrong and Amélie Loher. All rights reserved.
-- Released under Apache 2.0 license as described in the file LICENSE.
module

public import RothschildStein.Definitions.hasWeakWordDeriv

set_option autoImplicit false
set_option relaxedAutoImplicit false
@[expose] public section
noncomputable section
namespace RothschildStein.P1

/-- Word transposes commute with generator reindexing. -/
theorem wordTranspose_map_indices {a b n : ℕ}
    (X : Fin b → (Fin n → ℝ) → (Fin n → ℝ)) (e : Fin a → Fin b)
    (I : List (Fin a)) (φ : (Fin n → ℝ) → ℝ) :
    wordTranspose X (I.map e) φ = wordTranspose (X ∘ e) I φ := by
  induction I generalizing φ with
  | nil => rfl
  | cons i I ih =>
      simpa only [List.map_cons, wordTranspose, Function.comp_apply] using
        ih (fieldTranspose (X (e i)) φ)

/-- Weak word derivatives retain their exact meaning when
original generator indices are embedded in a larger family. -/
theorem hasWeakWordDeriv_map_indices_iff {a b n : ℕ}
    (X : Fin b → (Fin n → ℝ) → (Fin n → ℝ)) (e : Fin a → Fin b)
    (Ω : TopologicalSpace.Opens (Fin n → ℝ)) (I : List (Fin a))
    (f g : (Fin n → ℝ) → ℝ) :
    hasWeakWordDeriv X Ω (I.map e) f g ↔ hasWeakWordDeriv (X ∘ e) Ω I f g := by
  simp only [hasWeakWordDeriv, wordTranspose_map_indices]

end RothschildStein.P1

-- Copyright (c) 2026 Scott Armstrong and Amélie Loher. All rights reserved.
-- Released under Apache 2.0 license as described in the file LICENSE.
module

public import RothschildStein.S.WeakDeriv

set_option autoImplicit false
set_option relaxedAutoImplicit false
set_option backward.isDefEq.respectTransparency false
@[expose] public section
noncomputable section
open Set MeasureTheory TopologicalSpace
open scoped BigOperators
namespace RothschildStein.P1

private theorem fieldTranspose_zero_function {n : ℕ}
    (X : (Fin n → ℝ) → (Fin n → ℝ)) :
    fieldTranspose X (fun _ => (0 : ℝ)) = 0 := by
  funext x
  simp [fieldTranspose, Hormander.Interface.euclideanDivergence]

private theorem fieldTranspose_zero_field {n : ℕ}
    (f : (Fin n → ℝ) → ℝ) : fieldTranspose (fun _ => (0 : Fin n → ℝ)) f = 0 := by
  funext x
  simp [fieldTranspose, Hormander.Interface.euclideanDivergence]

private theorem wordTranspose_zero_function {n q : ℕ}
    (X : Fin q → (Fin n → ℝ) → (Fin n → ℝ)) (I : List (Fin q)) :
    wordTranspose X I (fun _ => (0 : ℝ)) = 0 := by
  induction I with
  | nil => rfl
  | cons i I ih =>
    simp only [wordTranspose, fieldTranspose_zero_function]
    exact ih

/-- A word containing a zero field has identically zero
transpose on every function. This is an analytic alphabet adapter,
not a free-model dimension padding. -/
theorem wordTranspose_eq_zero_of_zero_field_mem {n q : ℕ}
    (X : Fin q → (Fin n → ℝ) → (Fin n → ℝ))
    (I : List (Fin q)) (i : Fin q) (hi : i ∈ I) (hX : X i = 0)
    (f : (Fin n → ℝ) → ℝ) : wordTranspose X I f = 0 := by
  induction I generalizing f with
  | nil => simp at hi
  | cons j I ih =>
    rcases List.mem_cons.mp hi with he | hi
    · subst j
      simp only [wordTranspose, hX]
      rw [show fieldTranspose (0 : (Fin n → ℝ) → (Fin n → ℝ)) f = 0 from
        fieldTranspose_zero_field f]
      exact wordTranspose_zero_function X I
    · exact ih hi (fieldTranspose (X j) f)

/-- Every locally integrable function has zero weak derivative
along a word containing a zero field. Used only for the forcing-space
adapter to the genuine diffusion-padded system. -/
theorem hasWeakWordDeriv_zero_of_zero_field_mem {n q : ℕ}
    (X : Fin q → (Fin n → ℝ) → (Fin n → ℝ))
    (Ω : Opens (Fin n → ℝ)) (I : List (Fin q)) (i : Fin q)
    (hi : i ∈ I) (hX : X i = 0) (f : (Fin n → ℝ) → ℝ)
    (hf : LocallyIntegrableOn f (Ω : Set (Fin n → ℝ)) volume) :
    hasWeakWordDeriv X Ω I f (fun _ => 0) := by
  refine ⟨hf, locallyIntegrableOn_zero, ?_⟩
  intro φ
  rw [wordTranspose_eq_zero_of_zero_field_mem X I i hi hX]
  simp

end RothschildStein.P1

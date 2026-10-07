-- Copyright (c) 2026 Scott Armstrong and Amélie Loher. All rights reserved.
-- Released under Apache 2.0 license as described in the file LICENSE.
module
public import RothschildStein.L1.LiftDimensionIncrease
@[expose] public section
set_option autoImplicit false
set_option relaxedAutoImplicit false
noncomputable section
open scoped BigOperators
namespace RothschildStein.L1

/-- Every field system is free at cutoff zero: its only bounded
word is empty and both actual and formal commutators vanish. -/
theorem freeAt_zero {a n : ℕ} (p : Fin a → ℕ+)
    (X : Fin a → (Fin n → ℝ) → (Fin n → ℝ)) (x : Fin n → ℝ) :
    FreeAt p 0 X x := by
  intro c
  have he : ∀ I : BoundedWord a 0 p, boundedWordList I = [] := by
    intro I
    exact (G3.weight_eq_zero_iff p _).mp (Nat.eq_zero_of_le_zero (G3.boundedWord_weight I))
  have ha : (∑ I : BoundedWord a 0 p, c I • wordBracket X (boundedWordList I) x) = 0 := by
    simp only [he,wordBracket,Pi.zero_apply,smul_zero,Finset.sum_const_zero]
  have hf : FormalRelation c := by
    unfold FormalRelation
    have hz : ∀ I : BoundedWord a 0 p,
        (truncatedBracket (boundedWordList I) : WordCoefficients a 0 p) = 0 := by
      intro I
      funext J
      rw [truncatedBracket,he I]
      rfl
    simp only [hz,smul_zero,Finset.sum_const_zero]
  exact ⟨fun _ => hf,fun _ => ha⟩

/-- Failure at the working cutoff has a first positive weighted
cutoff of failure, whose preceding cutoff remains free (BB Theorem 10.19). -/
theorem exists_first_freeness_defect {a s n : ℕ} (p : Fin a → ℕ+)
    (X : Fin a → (Fin n → ℝ) → (Fin n → ℝ)) (x : Fin n → ℝ)
    (hnot : ¬ FreeAt p s X x) :
    ∃ σ : ℕ, 1 ≤ σ ∧ σ ≤ s ∧ FreeAt p (σ-1) X x ∧ ¬ FreeAt p σ X x := by
  classical
  have h : ∃ σ : ℕ, ¬ FreeAt p σ X x := ⟨s,hnot⟩
  let σ := Nat.find h
  have hbad : ¬ FreeAt p σ X x := Nat.find_spec h
  have hpos : 1 ≤ σ := by
    by_contra hn
    have hz : σ = 0 := by omega
    rw [hz] at hbad
    exact hbad (freeAt_zero p X x)
  refine ⟨σ,hpos,Nat.find_min' h hnot,?_,hbad⟩
  exact not_not.mp (Nat.find_min h (show σ-1 < σ by omega))
end RothschildStein.L1

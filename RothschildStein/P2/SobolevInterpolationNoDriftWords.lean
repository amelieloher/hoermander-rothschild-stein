-- Copyright (c) 2026 Scott Armstrong and Amélie Loher. All rights reserved.
-- Released under Apache 2.0 license as described in the file LICENSE.
module

public import RothschildStein.P2.SobolevInterpolationWords

/-!
# Sobolev interpolation without drift, seminorm absorption: the words of weight one and two

In a no-drift alphabet (`Fin q`, all weights one) the words of weight one are the letters `[l]`, and the
words `[l, l]` have weight two, so a sum over the words of weight two dominates the sum over them
(the seminorms `Φ_j` of `SobolevInterpolationWords` are alphabet-generic).
-/

set_option autoImplicit false
set_option relaxedAutoImplicit false

@[expose] public section
noncomputable section
open Set MeasureTheory TopologicalSpace Filter
open scoped BigOperators Topology ENNReal
namespace RothschildStein.P2

open RothschildStein

section NoDrift

variable {q : ℕ} {w : Fin q → ℕ+}

/-- In a no-drift alphabet the words of weight one are the letters `[l]`. -/
theorem wordsOfWeight_one_noDrift (hw : ∀ j, (w j : ℕ) = 1) :
    wordsOfWeight w 1 = Finset.univ.image (fun l : Fin q => [l]) := by
  ext I
  rw [mem_wordsOfWeight, Finset.mem_image]
  constructor
  · intro h
    have hlen := S.length_le_wordWeight w I
    rw [h] at hlen
    rcases I with _ | ⟨i, _ | ⟨j, I'⟩⟩
    · simp [wordWeight] at h
    · exact ⟨i, Finset.mem_univ _, rfl⟩
    · simp at hlen
  · rintro ⟨l, -, rfl⟩
    simp [wordWeight, hw l]

/-- A sum over the words of weight one is the sum over the letters (no drift). -/
theorem sum_wordsOfWeight_one_noDrift (hw : ∀ j, (w j : ℕ) = 1)
    {M : Type*} [AddCommMonoid M] (f : List (Fin q) → M) :
    ∑ I ∈ wordsOfWeight w 1, f I = ∑ l : Fin q, f [l] := by
  rw [wordsOfWeight_one_noDrift hw, Finset.sum_image]
  intro l _ l' _ h
  exact List.singleton_injective h

/-- The words `[l, l]` have weight two, so a sum over the words of weight two dominates the sum
over them (no drift). -/
theorem sum_wordsOfWeight_two_ge_noDrift (hw : ∀ j, (w j : ℕ) = 1)
    (f : List (Fin q) → ℝ≥0∞) :
    ∑ l : Fin q, f [l, l] ≤ ∑ I ∈ wordsOfWeight w 2, f I := by
  classical
  set T : Finset (List (Fin q)) := Finset.univ.image (fun l : Fin q => [l, l]) with hT
  have hsub : T ⊆ wordsOfWeight w 2 := by
    intro I hI
    rw [hT, Finset.mem_image] at hI
    rw [mem_wordsOfWeight]
    rcases hI with ⟨l, -, rfl⟩
    simp [wordWeight, hw l]
  have hinj : Set.InjOn (fun l : Fin q => [l, l]) (Finset.univ : Finset (Fin q)) := by
    intro l _ l' _ h
    exact (List.cons.inj h).1
  calc ∑ l : Fin q, f [l, l] = ∑ I ∈ T, f I := by
        rw [hT, Finset.sum_image hinj]
    _ ≤ _ := Finset.sum_le_sum_of_subset hsub

end NoDrift

end RothschildStein.P2

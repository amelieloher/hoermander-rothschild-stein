-- Copyright (c) 2026 Scott Armstrong and Amélie Loher. All rights reserved.
-- Released under Apache 2.0 license as described in the file LICENSE.
module

public import RothschildStein.G4.ShortFields
public import RothschildStein.Definitions.BoundedWord

@[expose] public section
set_option autoImplicit false
set_option relaxedAutoImplicit false
noncomputable section
open Set

namespace RothschildStein.L1

/-- The empty bounded word contributes zero, so actual
bounded-word spanning implies the nonempty bracket-step predicate `bracketStepOn`. -/
theorem bracketStepOn_of_bounded_word_spans {a n s : ℕ}
    (Ω : Set (Fin n → ℝ)) (w : Fin a → ℕ+)
    (X : Fin a → (Fin n → ℝ) → (Fin n → ℝ))
    (hspan : ∀ x ∈ Ω, Submodule.span ℝ (range (fun I : BoundedWord a s w =>
      wordBracket X (boundedWordList I) x)) = ⊤) : bracketStepOn Ω w X s := by
  intro x hx
  apply top_unique
  rw [← hspan x hx]
  apply Submodule.span_le.mpr
  rintro _ ⟨I, rfl⟩
  by_cases hI : boundedWordList I = []
  · simp only [hI, wordBracket]
    exact Submodule.zero_mem _
  · apply Submodule.subset_span
    exact ⟨boundedWordList I, hI, G3.boundedWord_weight I, rfl⟩

/-- The bracket-step hypothesis gives the exact
bounded-word span consumed by the fixed free-lift construction. -/
theorem bounded_word_span_eq_top_of_bracketStepOn {a n s : ℕ}
    {Ω : Set (Fin n → ℝ)} {w : Fin a → ℕ+}
    {X : Fin a → (Fin n → ℝ) → (Fin n → ℝ)}
    (hstep : bracketStepOn Ω w X s) {x : Fin n → ℝ} (hx : x ∈ Ω) :
    Submodule.span ℝ (range (fun I : BoundedWord a s w =>
      wordBracket X (boundedWordList I) x)) = ⊤ := by
  apply top_unique
  rw [← hstep x hx]
  apply Submodule.span_le.mpr
  rintro _ ⟨I, _, hI, rfl⟩
  exact Submodule.subset_span ⟨⟨I, (G3.mem_wordFamily_iff w I).mpr hI⟩, rfl⟩

end RothschildStein.L1

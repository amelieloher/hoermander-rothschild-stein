-- Copyright (c) 2026 Scott Armstrong and Amélie Loher. All rights reserved.
-- Released under Apache 2.0 license as described in the file LICENSE.
module
public import RothschildStein.L1.DirectEvaluationRank
@[expose] public section
set_option autoImplicit false
set_option relaxedAutoImplicit false
noncomputable section
open Set TopologicalSpace
open scoped BigOperators
namespace RothschildStein.L1

/-- The direct formal evaluation range is exactly the actual
bounded word span, with no restriction on individual generator weights. -/
theorem directPointEvaluation_range_eq_word_span {a s n : ℕ} {p : Fin a → ℕ+}
    (Ω : Opens (Fin n → ℝ))
    (X : Fin a → (Fin n → ℝ) → (Fin n → ℝ))
    (hX : ∀ i, ContDiffOn ℝ (⊤ : ℕ∞) (X i) Ω)
    {x : Fin n → ℝ} (hx : x ∈ Ω) :
    LinearMap.range (directPointEvaluation (s := s) (p := p) Ω X hX x) =
      Submodule.span ℝ (range (fun I : BoundedWord a s p =>
        wordBracket X (boundedWordList I) x)) := by
  apply le_antisymm
  · rintro _ ⟨f,rfl⟩
    obtain ⟨c,rfl⟩ := formalWordCoefficientMap_surjective_unrestricted f
    rw [directPointEvaluation_formalWordCoefficients Ω X hX c hx]
    apply Submodule.sum_mem
    intro I _
    exact Submodule.smul_mem _ _ (Submodule.subset_span ⟨I,rfl⟩)
  · apply Submodule.span_le.mpr
    rintro _ ⟨I,rfl⟩
    exact ⟨G3.wordLieElement (boundedWordList I),
      directPointEvaluation_word Ω X hX _ (G3.boundedWord_weight I) hx⟩

/-- Freeness in the full formal dimension forces spanning. -/
theorem word_span_eq_top_of_freeAt_and_dimension_eq {a s n : ℕ} {p : Fin a → ℕ+}
    (Ω : Opens (Fin n → ℝ))
    (X : Fin a → (Fin n → ℝ) → (Fin n → ℝ))
    (hX : ∀ i, ContDiffOn ℝ (⊤ : ℕ∞) (X i) Ω)
    {x : Fin n → ℝ} (hx : x ∈ Ω) (hf : FreeAt p s X x)
    (hd : n = freeDimension a s p) :
    Submodule.span ℝ (range (fun I : BoundedWord a s p =>
      wordBracket X (boundedWordList I) x)) = ⊤ := by
  rw [← directPointEvaluation_range_eq_word_span Ω X hX hx]
  apply Submodule.eq_top_of_finrank_eq
  rw [finrank_directPointEvaluation_range_of_freeAt Ω X hX hx hf]
  simpa using hd.symm
end RothschildStein.L1

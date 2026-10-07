-- Copyright (c) 2026 Scott Armstrong and Amélie Loher. All rights reserved.
-- Released under Apache 2.0 license as described in the file LICENSE.
module
public import RothschildStein.L1.TranslationFields
public import RothschildStein.Definitions.FreeAt
@[expose] public section
set_option autoImplicit false
set_option relaxedAutoImplicit false
noncomputable section
open Set TopologicalSpace
namespace RothschildStein.L1

/-- Recentring preserves the freeness predicate `FreeAt`. -/
theorem translatedFields_freeAt_iff {a s n : ℕ} {p : Fin a → ℕ+}
    (Ω : Opens (Fin n → ℝ))
    (X : Fin a → (Fin n → ℝ) → (Fin n → ℝ))
    (hX : ∀ i, ContDiffOn ℝ (⊤ : ℕ∞) (X i) Ω)
    (t x : Fin n → ℝ) (hx : x+t ∈ Ω) :
    FreeAt p s (translatedFields X t) x ↔ FreeAt p s X (x+t) := by
  unfold FreeAt
  simp only [translatedFields_wordBracket Ω X hX t _ x hx]

/-- Recentring preserves the span of the bounded words. -/
theorem translatedFields_word_span {a s n : ℕ} {p : Fin a → ℕ+}
    (Ω : Opens (Fin n → ℝ))
    (X : Fin a → (Fin n → ℝ) → (Fin n → ℝ))
    (hX : ∀ i, ContDiffOn ℝ (⊤ : ℕ∞) (X i) Ω)
    (t x : Fin n → ℝ) (hx : x+t ∈ Ω) :
    Submodule.span ℝ (range (fun I : BoundedWord a s p =>
      wordBracket (translatedFields X t) (boundedWordList I) x)) =
    Submodule.span ℝ (range (fun I : BoundedWord a s p =>
      wordBracket X (boundedWordList I) (x+t))) := by
  simp only [translatedFields_wordBracket Ω X hX t _ x hx]
end RothschildStein.L1

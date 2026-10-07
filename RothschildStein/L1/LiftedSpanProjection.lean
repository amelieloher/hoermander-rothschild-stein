-- Copyright (c) 2026 Scott Armstrong and Amélie Loher. All rights reserved.
-- Released under Apache 2.0 license as described in the file LICENSE.
module
public import RothschildStein.L1.LiftedBracketProjection
@[expose] public section
set_option autoImplicit false
set_option relaxedAutoImplicit false
noncomputable section
open Set TopologicalSpace
namespace RothschildStein.L1

/-- The horizontal image of the bounded lifted
word span is exactly the original bounded word span, at every cutoff. -/
theorem oneVariableLift_word_span_map {a s n : ℕ} {p : Fin a → ℕ+}
    (Ω : Opens (Fin n → ℝ))
    (X : Fin a → (Fin n → ℝ) → (Fin n → ℝ))
    (hX : ∀ i, ContDiffOn ℝ (⊤ : ℕ∞) (X i) Ω)
    (u : Fin a → (Fin n → ℝ) → ℝ)
    (hu : ∀ i, ContDiffOn ℝ (⊤ : ℕ∞) (u i) Ω)
    {ξ : Fin (n+1) → ℝ} (hξ : P1.paddingBaseCLM n 1 ξ ∈ Ω) :
    (Submodule.span ℝ (range (fun I : BoundedWord a s p =>
      wordBracket (oneVariableLift X u) (boundedWordList I) ξ))).map
        (P1.paddingBaseCLM n 1).toLinearMap =
    Submodule.span ℝ (range (fun I : BoundedWord a s p =>
      wordBracket X (boundedWordList I) (P1.paddingBaseCLM n 1 ξ))) := by
  rw [Submodule.map_span,← Set.range_comp]
  congr 1
  congr 1
  funext I
  exact oneVariableLift_wordBracket_base Ω X hX u hu _ hξ
end RothschildStein.L1

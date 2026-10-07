-- Copyright (c) 2026 Scott Armstrong and Amélie Loher. All rights reserved.
-- Released under Apache 2.0 license as described in the file LICENSE.
module
public import RothschildStein.L1.DirectEvaluation
@[expose] public section
set_option autoImplicit false
set_option relaxedAutoImplicit false
noncomputable section
open Set TopologicalSpace
open scoped BigOperators
namespace RothschildStein.L1
open G3

/-- Tangent combinations of word values factor through formal evaluation. -/
theorem directPointEvaluation_formalWordCoefficients {a s N : ℕ} {p : Fin a → ℕ+}
    (Ω : Opens (Fin N → ℝ))
    (X : Fin a → (Fin N → ℝ) → (Fin N → ℝ))
    (hX : ∀ i, ContDiffOn ℝ (⊤ : ℕ∞) (X i) Ω)
    (c : BoundedWord a s p → ℝ) {x : Fin N → ℝ} (hx : x ∈ Ω) :
    directPointEvaluation (s := s) (p := p) Ω X hX x (formalWordCoefficientMap c) =
      ∑ I, c I • wordBracket X (boundedWordList I) x := by
  change directPointEvaluation (s := s) (p := p) Ω X hX x (∑ I, c I • wordLieElement (boundedWordList I)) = _
  rw [map_sum]
  apply Finset.sum_congr rfl
  intro I _
  rw [map_smul,directPointEvaluation_word Ω X hX _ (boundedWord_weight I) hx]

/-- The freeness predicate `FreeAt` is exactly injectivity of tangent evaluation
(BB Definition 10.10 and Proposition 10.14, pp. 487–490). -/
theorem freeAt_iff_directPointEvaluation_injective {a s N : ℕ} {p : Fin a → ℕ+}
    (Ω : Opens (Fin N → ℝ))
    (X : Fin a → (Fin N → ℝ) → (Fin N → ℝ))
    (hX : ∀ i, ContDiffOn ℝ (⊤ : ℕ∞) (X i) Ω)
    {x : Fin N → ℝ} (hx : x ∈ Ω) :
    FreeAt p s X x ↔ Function.Injective (directPointEvaluation (s := s) (p := p) Ω X hX x) := by
  constructor
  · intro hfree
    apply LinearMap.ker_eq_bot.mp
    apply LinearMap.ker_eq_bot'.mpr
    intro f hf
    obtain ⟨c,rfl⟩ := formalWordCoefficientMap_surjective_unrestricted f
    apply (formalWordCoefficientMap_eq_zero_iff c).mpr
    apply (hfree c).mp
    rw [← directPointEvaluation_formalWordCoefficients Ω X hX c hx]
    exact hf
  · intro hinj c
    rw [← directPointEvaluation_formalWordCoefficients Ω X hX c hx]
    rw [← formalWordCoefficientMap_eq_zero_iff c]
    exact ⟨fun h => hinj (h.trans (map_zero _).symm),fun h => by rw [h,map_zero]⟩
end RothschildStein.L1

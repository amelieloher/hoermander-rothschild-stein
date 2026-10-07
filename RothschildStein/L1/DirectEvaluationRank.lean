-- Copyright (c) 2026 Scott Armstrong and Amélie Loher. All rights reserved.
-- Released under Apache 2.0 license as described in the file LICENSE.
module
public import RothschildStein.L1.DirectFreeness
public import Mathlib.LinearAlgebra.Dimension.Finrank
@[expose] public section
set_option autoImplicit false
set_option relaxedAutoImplicit false
noncomputable section
open Set TopologicalSpace
namespace RothschildStein.L1
open G3

/-- Freeness gives the full formal rank in the tangent image
(BB Proposition 10.14(ii), pp. 489–490). -/
theorem finrank_directPointEvaluation_range_of_freeAt {a s N : ℕ} {p : Fin a → ℕ+}
    (Ω : Opens (Fin N → ℝ))
    (X : Fin a → (Fin N → ℝ) → (Fin N → ℝ))
    (hX : ∀ i, ContDiffOn ℝ (⊤ : ℕ∞) (X i) Ω)
    {x : Fin N → ℝ} (hx : x ∈ Ω) (hf : FreeAt p s X x) :
    Module.finrank ℝ (LinearMap.range (directPointEvaluation (s := s) (p := p) Ω X hX x)) = freeDimension a s p :=
  LinearMap.finrank_range_of_inj ((freeAt_iff_directPointEvaluation_injective Ω X hX hx).mp hf)

/-- A free tangent evaluation bounds the formal rank by the ambient dimension. -/
theorem freeDimension_le_of_freeAt_unrestricted {a s N : ℕ} {p : Fin a → ℕ+}
    (Ω : Opens (Fin N → ℝ))
    (X : Fin a → (Fin N → ℝ) → (Fin N → ℝ))
    (hX : ∀ i, ContDiffOn ℝ (⊤ : ℕ∞) (X i) Ω)
    {x : Fin N → ℝ} (hx : x ∈ Ω) (hf : FreeAt p s X x) : freeDimension a s p ≤ N := by
  have he := LinearMap.finrank_le_finrank_of_injective
    ((freeAt_iff_directPointEvaluation_injective Ω X hX hx).mp hf)
  simpa [freeDimension] using he

/-- Spanning of the word values makes formal tangent evaluation surjective. -/
theorem directPointEvaluation_surjective_of_word_span {a s N : ℕ} {p : Fin a → ℕ+}
    (Ω : Opens (Fin N → ℝ))
    (X : Fin a → (Fin N → ℝ) → (Fin N → ℝ))
    (hX : ∀ i, ContDiffOn ℝ (⊤ : ℕ∞) (X i) Ω)
    {x : Fin N → ℝ} (hx : x ∈ Ω)
    (hspan : Submodule.span ℝ (range (fun I : BoundedWord a s p =>
      wordBracket X (boundedWordList I) x)) = ⊤) :
    Function.Surjective (directPointEvaluation (s := s) (p := p) Ω X hX x) := by
  apply LinearMap.range_eq_top.mp
  apply top_unique
  rw [← hspan]
  apply Submodule.span_le.mpr
  rintro _ ⟨I,rfl⟩
  exact ⟨wordLieElement (boundedWordList I),
    directPointEvaluation_word Ω X hX _ (boundedWord_weight I) hx⟩

/-- A spanning tangent system cannot exceed the formal rank. -/
theorem dimension_le_freeDimension_of_word_span_unrestricted {a s N : ℕ} {p : Fin a → ℕ+}
    (Ω : Opens (Fin N → ℝ))
    (X : Fin a → (Fin N → ℝ) → (Fin N → ℝ))
    (hX : ∀ i, ContDiffOn ℝ (⊤ : ℕ∞) (X i) Ω)
    {x : Fin N → ℝ} (hx : x ∈ Ω)
    (hspan : Submodule.span ℝ (range (fun I : BoundedWord a s p =>
      wordBracket X (boundedWordList I) x)) = ⊤) : N ≤ freeDimension a s p := by
  have he := LinearMap.finrank_le_finrank_of_surjective
    (directPointEvaluation_surjective_of_word_span Ω X hX hx hspan)
  simpa [freeDimension] using he
end RothschildStein.L1

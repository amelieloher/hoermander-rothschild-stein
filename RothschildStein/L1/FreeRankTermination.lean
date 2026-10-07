-- Copyright (c) 2026 Scott Armstrong and Amélie Loher. All rights reserved.
-- Released under Apache 2.0 license as described in the file LICENSE.
module
public import RothschildStein.L1.DirectEvaluationRank
public import RothschildStein.L1.FirstFreenessDefect
@[expose] public section
set_option autoImplicit false
set_option relaxedAutoImplicit false
noncomputable section
open Set TopologicalSpace
namespace RothschildStein.L1

/-- A spanning tangent evaluation is free when the ambient
rank reaches the formal dimension; no further lift is possible
(BB Theorem 10.19, pp. 493–494). -/
theorem freeAt_of_spanning_and_dimension_eq {a s n : ℕ} {p : Fin a → ℕ+}
    (Ω : Opens (Fin n → ℝ))
    (X : Fin a → (Fin n → ℝ) → (Fin n → ℝ))
    (hX : ∀ i, ContDiffOn ℝ (⊤ : ℕ∞) (X i) Ω)
    {x : Fin n → ℝ} (hx : x ∈ Ω)
    (hspan : Submodule.span ℝ (range (fun I : BoundedWord a s p =>
      wordBracket X (boundedWordList I) x)) = ⊤)
    (hdim : n = freeDimension a s p) : FreeAt p s X x := by
  have he : Module.finrank ℝ (formalSpan a s p) = Module.finrank ℝ (Fin n → ℝ) := by
    simpa [freeDimension] using hdim.symm
  apply (freeAt_iff_directPointEvaluation_injective Ω X hX hx).mpr
  exact (LinearMap.injective_iff_surjective_of_finrank_eq_finrank he).mpr
    (directPointEvaluation_surjective_of_word_span Ω X hX hx hspan)

/-- A spanning but nonfree system has strictly smaller ambient
dimension than the formal rank, so the next one-variable lift fits within
that rank (BB Theorem 10.19). -/
theorem dimension_lt_freeDimension_of_nonfree_spanning {a s n : ℕ} {p : Fin a → ℕ+}
    (Ω : Opens (Fin n → ℝ))
    (X : Fin a → (Fin n → ℝ) → (Fin n → ℝ))
    (hX : ∀ i, ContDiffOn ℝ (⊤ : ℕ∞) (X i) Ω)
    {x : Fin n → ℝ} (hx : x ∈ Ω)
    (hspan : Submodule.span ℝ (range (fun I : BoundedWord a s p =>
      wordBracket X (boundedWordList I) x)) = ⊤)
    (hn : ¬ FreeAt p s X x) : n < freeDimension a s p := by
  have hle := dimension_le_freeDimension_of_word_span_unrestricted Ω X hX hx hspan
  have hne : n ≠ freeDimension a s p := by
    intro he
    exact hn (freeAt_of_spanning_and_dimension_eq Ω X hX hx hspan he)
  omega
end RothschildStein.L1

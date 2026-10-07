-- Copyright (c) 2026 Scott Armstrong and Amélie Loher. All rights reserved.
-- Released under Apache 2.0 license as described in the file LICENSE.
module
public import RothschildStein.L1.DirectFreeness
@[expose] public section
set_option autoImplicit false
set_option relaxedAutoImplicit false
noncomputable section
open Set TopologicalSpace
open scoped BigOperators
namespace RothschildStein.L1
open G3

/-- Failure of freeness gives a genuine tangent
relation whose complete formal coefficient vector is nonzero
(BB Proposition 10.17, pp. 490–492). -/
theorem exists_nonformal_tangent_relation {a s N : ℕ} {p : Fin a → ℕ+}
    (Ω : Opens (Fin N → ℝ)) (X : Fin a → (Fin N → ℝ) → (Fin N → ℝ))
    (hX : ∀ i, ContDiffOn ℝ (⊤ : ℕ∞) (X i) Ω)
    {x : Fin N → ℝ} (hx : x ∈ Ω) (hnot : ¬ FreeAt p s X x) :
    ∃ c : WordCoefficients a s p,
      (∑ I, c I • wordBracket X (boundedWordList I) x) = 0 ∧ ¬ FormalRelation c := by
  classical
  let T := directPointEvaluation (s := s) (p := p) Ω X hX x
  have he : ∃ f : formalSpan a s p, T f = 0 ∧ f ≠ 0 := by
    by_contra hn
    have hzero : ∀ f : formalSpan a s p, T f = 0 → f = 0 := by
      intro f hf
      by_contra hne
      exact hn ⟨f,hf,hne⟩
    have hi : Function.Injective T := LinearMap.ker_eq_bot.mp (LinearMap.ker_eq_bot'.mpr hzero)
    exact hnot ((freeAt_iff_directPointEvaluation_injective Ω X hX hx).mpr hi)
  obtain ⟨f,hf,hne⟩ := he
  obtain ⟨c,hc⟩ := formalWordCoefficientMap_surjective_unrestricted f
  refine ⟨c,?_,?_⟩
  · rw [← directPointEvaluation_formalWordCoefficients Ω X hX c hx,hc]
    exact hf
  · intro hrel
    have hz := (formalWordCoefficientMap_eq_zero_iff c).mpr hrel
    rw [hc] at hz
    exact hne hz

/-- A nonformal relation has a nonzero associative
word coefficient, the coefficient selected for the vertical jet prescription. -/
theorem exists_nonzero_formal_relation_coefficient {a s : ℕ} {p : Fin a → ℕ+}
    (c : WordCoefficients a s p) (hnot : ¬ FormalRelation c) :
    ∃ J : BoundedWord a s p,
      (∑ I, c I * truncatedBracket (boundedWordList I) J) ≠ 0 := by
  classical
  have hne : (∑ I, c I • (truncatedBracket (boundedWordList I) : WordCoefficients a s p)) ≠ 0 := hnot
  obtain ⟨J,hJ⟩ := Function.ne_iff.mp hne
  refine ⟨J,?_⟩
  simpa only [Finset.sum_apply,Pi.smul_apply,smul_eq_mul,Pi.zero_apply] using hJ
end RothschildStein.L1

-- Copyright (c) 2026 Scott Armstrong and Amélie Loher. All rights reserved.
-- Released under Apache 2.0 license as described in the file LICENSE.
module
public import RothschildStein.L1.LiftedRelationWitness
public import RothschildStein.L1.OneVariableSpanRank
public import RothschildStein.L1.LiftedSpanProjection
@[expose] public section
set_option autoImplicit false
set_option relaxedAutoImplicit false
noncomputable section
open Set TopologicalSpace
open scoped BigOperators
namespace RothschildStein.L1

/-- The polynomial one-variable lift preserves lower freeness and
increases every word-span rank at and above the defective cutoff by exactly
one (BB Proposition 10.17, pp. 490–493). -/
theorem exists_polynomial_lift_with_rank_increase {a σ n : ℕ} {p : Fin a → ℕ+}
    (Ω : Opens (Fin n → ℝ))
    (X : Fin a → (Fin n → ℝ) → (Fin n → ℝ))
    (hX : ∀ i, ContDiffOn ℝ (⊤ : ℕ∞) (X i) Ω)
    (hzero : (0 : Fin n → ℝ) ∈ Ω)
    (hf : FreeAt p (σ-1) X 0) (hnot : ¬ FreeAt p σ X 0) :
    ∃ U : Fin a → MvPolynomial (Fin n) ℝ,
      let Y := oneVariableLift X (fun j x => MvPolynomial.eval x (U j))
      FreeAt p (σ-1) Y 0 ∧ ∀ k, σ ≤ k →
        Module.finrank ℝ (Submodule.span ℝ (range (fun I : BoundedWord a k p =>
          wordBracket Y (boundedWordList I) 0))) =
        Module.finrank ℝ (Submodule.span ℝ (range (fun I : BoundedWord a k p =>
          wordBracket X (boundedWordList I) 0))) + 1 := by
  classical
  obtain ⟨U,c,hfree,hbase,hvert⟩ := exists_polynomial_lift_with_vertical_relation Ω X hX hzero hf hnot
  let u : Fin a → (Fin n → ℝ) → ℝ := fun j x => MvPolynomial.eval x (U j)
  let Y := oneVariableLift X u
  have hu : ∀ i, ContDiffOn ℝ (⊤ : ℕ∞) (u i) Ω :=
    fun i => (contDiff_polynomial_eval (U i)).contDiffOn
  refine ⟨U,hfree,?_⟩
  intro k hk
  let S := Submodule.span ℝ (range (fun I : BoundedWord a k p =>
    wordBracket Y (boundedWordList I) 0))
  have hv : (∑ I : BoundedWord a σ p, c I • wordBracket Y (boundedWordList I) 0) ∈ S := by
    apply Submodule.sum_mem
    intro I _
    apply Submodule.smul_mem
    apply Submodule.subset_span
    refine ⟨G3.boundedWord p (boundedWordList I) ((G3.boundedWord_weight I).trans hk),?_⟩
    rfl
  have he := finrank_eq_base_add_one_of_vertical S hv hbase hvert
  have hz : P1.paddingBaseCLM n 1 (0 : Fin (n+1) → ℝ) ∈ Ω := by
    simpa only [map_zero] using hzero
  change Module.finrank ℝ S = _
  rw [he]
  rw [oneVariableLift_word_span_map Ω X hX u hu hz]
  rw [(P1.paddingBaseCLM n 1).map_zero]
end RothschildStein.L1

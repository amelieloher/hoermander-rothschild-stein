-- Copyright (c) 2026 Scott Armstrong and Amélie Loher. All rights reserved.
-- Released under Apache 2.0 license as described in the file LICENSE.
module
public import RothschildStein.L1.FreeRankTermination
@[expose] public section
set_option autoImplicit false
set_option relaxedAutoImplicit false
noncomputable section
open Set TopologicalSpace
namespace RothschildStein.L1

/-- A spanning nonfree system has an actual polynomial one-variable
lift that spans its entire new tangent space; the lifted coefficients are
smooth on the cylinder (BB Theorem 10.19, pp. 493–494). -/
theorem exists_spanning_polynomial_lift_step {a s n : ℕ} {p : Fin a → ℕ+}
    (Ω : Opens (Fin n → ℝ))
    (X : Fin a → (Fin n → ℝ) → (Fin n → ℝ))
    (hX : ∀ i, ContDiffOn ℝ (⊤ : ℕ∞) (X i) Ω)
    (hzero : (0 : Fin n → ℝ) ∈ Ω)
    (hspan : Submodule.span ℝ (range (fun I : BoundedWord a s p =>
      wordBracket X (boundedWordList I) 0)) = ⊤)
    (hn : ¬ FreeAt p s X 0) :
    ∃ U : Fin a → MvPolynomial (Fin n) ℝ,
      let Y := oneVariableLift X (fun j x => MvPolynomial.eval x (U j))
      (∀ i, ContDiffOn ℝ (⊤ : ℕ∞) (Y i) (oneVariableLiftDomain Ω)) ∧
      Submodule.span ℝ (range (fun I : BoundedWord a s p =>
        wordBracket Y (boundedWordList I) 0)) = ⊤ := by
  classical
  obtain ⟨σ,_,hσ,hf,hbad⟩ := exists_first_freeness_defect p X 0 hn
  obtain ⟨U,_,hrank⟩ := exists_polynomial_lift_with_rank_increase Ω X hX hzero hf hbad
  refine ⟨U,?_,?_⟩
  · exact oneVariableLift_contDiffOn Ω X hX _
      (fun i => (contDiff_polynomial_eval (U i)).contDiffOn)
  · apply Submodule.eq_top_of_finrank_eq
    have he := hrank s hσ
    rw [hspan] at he
    simpa using he
end RothschildStein.L1

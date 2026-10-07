-- Copyright (c) 2026 Scott Armstrong and Amélie Loher. All rights reserved.
-- Released under Apache 2.0 license as described in the file LICENSE.
module
public import RothschildStein.L1.LiftedBracketJets
public import RothschildStein.L1.LiftedBracketProjection
public import RothschildStein.L1.VerticalCoefficientChoice
public import RothschildStein.L1.TriangularSmoothness
@[expose] public section
set_option autoImplicit false
set_option relaxedAutoImplicit false
noncomputable section
open Set TopologicalSpace
open scoped BigOperators
namespace RothschildStein.L1

/-- A first defect in freeness yields polynomial vertical coefficients
and an actual nonzero vertical tangent combination. Lower freeness persists
(BB Proposition 10.17, pp. 490–493). -/
theorem exists_polynomial_lift_with_vertical_relation {a σ n : ℕ} {p : Fin a → ℕ+}
    (Ω : Opens (Fin n → ℝ))
    (X : Fin a → (Fin n → ℝ) → (Fin n → ℝ))
    (hX : ∀ i, ContDiffOn ℝ (⊤ : ℕ∞) (X i) Ω)
    (hzero : (0 : Fin n → ℝ) ∈ Ω)
    (hf : FreeAt p (σ-1) X 0) (hnot : ¬ FreeAt p σ X 0) :
    ∃ U : Fin a → MvPolynomial (Fin n) ℝ, ∃ c : WordCoefficients a σ p,
      let Y := oneVariableLift X (fun j x => MvPolynomial.eval x (U j))
      let v := ∑ I : BoundedWord a σ p, c I • wordBracket Y (boundedWordList I) 0
      FreeAt p (σ-1) Y 0 ∧ P1.paddingBaseCLM n 1 v = 0 ∧
        P1.paddingFiberCLM n 1 v 0 ≠ 0 := by
  classical
  obtain ⟨c,hc,hnc⟩ := exists_nonformal_tangent_relation Ω X hX hzero hnot
  obtain ⟨d,hd,hdetect⟩ := exists_vertical_jet_prescription c hnc
  obtain ⟨U,hY,hjets⟩ := exists_lift_with_vertical_word_jets Ω X hX hzero hf d hd
  let u : Fin a → (Fin n → ℝ) → ℝ := fun j x => MvPolynomial.eval x (U j)
  have hu : ∀ j, ContDiffOn ℝ (⊤ : ℕ∞) (u j) Ω := by
    intro j
    exact (contDiff_polynomial_eval (U j)).contDiffOn
  have hz : P1.paddingBaseCLM n 1 (0 : Fin (n+1) → ℝ) ∈ Ω := by
    simpa only [map_zero] using hzero
  refine ⟨U,c,?_,?_,?_⟩
  · exact oneVariableLift_freeAt_of_freeAt Ω X hX u hu hz (by simpa only [map_zero] using hf)
  · change P1.paddingBaseCLM n 1
      (∑ I : BoundedWord a σ p, c I • wordBracket (oneVariableLift X u) (boundedWordList I) 0) = 0
    simpa only [map_sum,map_smul,oneVariableLift_wordBracket_base Ω X hX u hu _ hz,
      map_zero] using hc
  · have hv : ∀ I : BoundedWord a σ p,
        P1.paddingFiberCLM n 1 (wordBracket (oneVariableLift X u) (boundedWordList I) 0) 0 =
          ∑ J : BoundedWord a σ p, truncatedBracket (boundedWordList I) J * d (boundedWordList J) := by
      intro I
      exact wordBracket_vertical_of_ordered_jets (oneVariableLiftDomain Ω)
        (oneVariableLift X u) hY hz d hjets _ (G3.boundedWord_weight I)
    change P1.paddingFiberCLM n 1
      (∑ I : BoundedWord a σ p, c I • wordBracket (oneVariableLift X u) (boundedWordList I) 0) 0 ≠ 0
    simpa only [map_sum,map_smul,Finset.sum_apply,Pi.smul_apply,smul_eq_mul,hv] using hdetect
end RothschildStein.L1

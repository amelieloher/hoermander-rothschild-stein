-- Copyright (c) 2026 Scott Armstrong and Amélie Loher. All rights reserved.
-- Released under Apache 2.0 license as described in the file LICENSE.
module
public import RothschildStein.G3.WeightedFiniteSubstitution
public import RothschildStein.G3.SubstitutionPolynomial
@[expose] public section
noncomputable section
namespace RothschildStein.G3

/-- Every source letter maps to its prescribed weighted input. -/
theorem weightedFiniteSubstitutionHom_letter {a b s : ℕ} {p : Fin b → ℕ+}
    (q : Fin a → ℕ+) (X : Fin a → FiniteWordAlgebra b s p)
    (hX : ∀ i, FiniteOrderAtLeast (q i : ℕ) (X i)) (i : Fin a) :
    weightedFiniteSubstitutionHom q X hX (finiteLetter i) = X i := by
  by_cases hi : (q i : ℕ) ≤ s
  · change polynomialEvaluation X
      (finitePolynomial (restrict (wordSeries [i]) : WordCoefficients a s q)) = X i
    rw [finitePolynomial_restrict_word [i] (by simpa only [wordWeight, List.map_singleton, List.sum_singleton] using hi)]
    change MonoidAlgebra.lift ℝ (FiniteWordAlgebra b s p) (FreeMonoid (Fin a))
      (FreeMonoid.lift X) (MonoidAlgebra.single (FreeMonoid.ofList [i]) (1 : ℝ)) = X i
    rw [MonoidAlgebra.lift_single, one_smul, FreeMonoid.ofList_singleton, FreeMonoid.lift_eval_of]
  · have hz : (finiteLetter (a := a) (s := s) (p := q) i) = 0 :=
      truncatedBracket_eq_zero_of_weight_gt [i] (by simp only [wordWeight, List.map_singleton, List.sum_singleton]; omega)
    rw [hz, map_zero]
    exact (eq_zero_of_finiteOrderAtLeast_gt (hX i) (by omega)).symm

/-- Weighted substitution commutes with finite BCH, allowing passage
between the primitive and the retained-bracket alphabets. -/
theorem weightedFiniteSubstitutionHom_bch {a b s : ℕ} {p : Fin b → ℕ+}
    (q : Fin a → ℕ+) (X : Fin a → FiniteWordAlgebra b s p)
    (hX : ∀ i, FiniteOrderAtLeast (q i : ℕ) (X i))
    {f g : FiniteWordAlgebra a s q} (hf : FiniteOrderAtLeast 1 f) (hg : FiniteOrderAtLeast 1 g) :
    weightedFiniteSubstitutionHom q X hX (finiteBCH f g) =
      finiteBCH (weightedFiniteSubstitutionHom q X hX f) (weightedFiniteSubstitutionHom q X hX g) :=
  map_finiteBCH _ (fun _ h => weightedFiniteSubstitutionHom_order q X hX h) hf hg
end RothschildStein.G3

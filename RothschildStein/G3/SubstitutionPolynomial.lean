-- Copyright (c) 2026 Scott Armstrong and Amélie Loher. All rights reserved.
-- Released under Apache 2.0 license as described in the file LICENSE.
module
public import RothschildStein.G3.FiniteSubstitution
@[expose] public section
noncomputable section
namespace RothschildStein.G3

/-- A word within the cutoff has its exact single-word polynomial
representative (BB pp. 467–468). -/
theorem finitePolynomial_restrict_word {a s : ℕ} {p : Fin a → ℕ+}
    (I : List (Fin a)) (hI : wordWeight p I ≤ s) :
    finitePolynomial (restrict (wordSeries I) : WordCoefficients a s p) =
      MonoidAlgebra.single (FreeMonoid.ofList I) 1 := by
  apply polynomialSeries_injective a
  rw [polynomialSeries_finitePolynomial, polynomialSeries_single, one_smul]
  funext J
  unfold extend
  split
  · rfl
  · rename_i hJ
    have hne : J ≠ I := by intro he; apply hJ; simpa only [he] using hI
    change 0 = (if J = I then (1 : ℝ) else 0)
    simp [hne]

/-- All finite letter generators have positive order (BB p. 468). -/
theorem finiteLetter_order {a s : ℕ} {p : Fin a → ℕ+} (i : Fin a) :
    FiniteOrderAtLeast 1 (finiteLetter (s := s) (p := p) i) := by
  apply (finite_positive_order_iff _).mpr
  exact formalBracket_constant_zero [i]

/-- Finite positive-order substitution sends every letter to the prescribed
input, including the zero-degree quotient (BB (9.75), p. 468). -/
theorem finiteSubstitutionHom_letter {a b s : ℕ} {p : Fin b → ℕ+}
    (X : Fin a → FiniteWordAlgebra b s p) (hX : ∀ i, FiniteOrderAtLeast 1 (X i)) (i : Fin a) :
    finiteSubstitutionHom X hX (finiteLetter i) = X i := by
  by_cases hs : 1 ≤ s
  · change polynomialEvaluation X
      (finitePolynomial (restrict (wordSeries [i]) : WordCoefficients a s (fun _ => 1))) = X i
    rw [finitePolynomial_restrict_word [i] (by simpa only [ordinary_weight, List.length_singleton] using hs)]
    change MonoidAlgebra.lift ℝ (FiniteWordAlgebra b s p) (FreeMonoid (Fin a))
      (FreeMonoid.lift X) (MonoidAlgebra.single (FreeMonoid.ofList [i]) 1) = X i
    rw [MonoidAlgebra.lift_single, one_smul, FreeMonoid.ofList_singleton, FreeMonoid.lift_eval_of]
  · have hs0 : s = 0 := by omega
    have he : (finiteLetter (a := a) (s := s) (p := fun _ => 1) i) = 0 :=
      truncatedBracket_eq_zero_of_weight_gt [i] (by simp [wordWeight, hs0])
    rw [he, map_zero]
    exact (eq_zero_of_finiteOrderAtLeast_gt (hX i) (by omega)).symm

end RothschildStein.G3

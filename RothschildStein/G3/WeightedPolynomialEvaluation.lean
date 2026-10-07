-- Copyright (c) 2026 Scott Armstrong and Amélie Loher. All rights reserved.
-- Released under Apache 2.0 license as described in the file LICENSE.
module
public import RothschildStein.G3.PolynomialEvaluation
@[expose] public section
noncomputable section
namespace RothschildStein.G3

/-- Substituting inputs of assigned positive weights preserves the
full source word weight (BB Lemma 9.22, pp. 413–414). -/
theorem wordEvaluation_weight_order {a b s : ℕ} {p : Fin b → ℕ+}
    (q : Fin a → ℕ+) (X : Fin a → FiniteWordAlgebra b s p)
    (hX : ∀ i, FiniteOrderAtLeast (q i : ℕ) (X i)) (I : List (Fin a)) :
    FiniteOrderAtLeast (wordWeight q I) (FreeMonoid.lift X (FreeMonoid.ofList I)) := by
  induction I with
  | nil => exact finiteOrderAtLeast_zero _
  | cons i I ih =>
    rw [FreeMonoid.ofList_cons, map_mul, FreeMonoid.lift_eval_of]
    simpa only [wordWeight, List.map_cons, List.sum_cons] using finiteOrderAtLeast_mul (hX i) ih

/-- Weighted polynomial substitution cannot lower the source
filtration order (BB Lemma 9.22, pp. 413–414). -/
theorem polynomialEvaluation_weight_order {a b s k : ℕ} {p : Fin b → ℕ+}
    (q : Fin a → ℕ+) (X : Fin a → FiniteWordAlgebra b s p)
    (hX : ∀ i, FiniteOrderAtLeast (q i : ℕ) (X i))
    (f : MonoidAlgebra ℝ (FreeMonoid (Fin a)))
    (hf : OrderAtLeast q k (polynomialSeries a f)) :
    FiniteOrderAtLeast k (polynomialEvaluation X f) := by
  classical
  change FiniteOrderAtLeast k
    (MonoidAlgebra.lift ℝ (FiniteWordAlgebra b s p) (FreeMonoid (Fin a)) (FreeMonoid.lift X) f)
  rw [MonoidAlgebra.lift_apply, Finsupp.sum]
  apply finiteOrderAtLeast_sum _ _
  intro I _
  by_cases hI : k ≤ wordWeight q I.toList
  · exact finiteOrderAtLeast_smul
      (finiteOrderAtLeast_mono (wordEvaluation_weight_order q X hX I.toList) hI) _
  · have hz := hf I.toList (by omega)
    rw [polynomialSeries_coeff, FreeMonoid.ofList_toList] at hz
    rw [hz, zero_smul]
    exact finiteOrderAtLeast_zero_element k

/-- A polynomial invisible through weighted degree s evaluates to
zero in a cutoff-s quotient under a weight-preserving substitution. -/
theorem polynomialEvaluation_eq_zero_of_weighted_truncate_zero {a b s : ℕ}
    {p : Fin b → ℕ+} (q : Fin a → ℕ+)
    (X : Fin a → FiniteWordAlgebra b s p)
    (hX : ∀ i, FiniteOrderAtLeast (q i : ℕ) (X i))
    (f : MonoidAlgebra ℝ (FreeMonoid (Fin a)))
    (hf : truncateSeries (s := s) (p := q) (polynomialSeries a f) = 0) :
    polynomialEvaluation X f = 0 := by
  apply eq_zero_of_finiteOrderAtLeast_gt (k := s + 1) ?_ (by omega)
  apply polynomialEvaluation_weight_order q X hX f
  intro I hI
  have hw : wordWeight q I ≤ s := by omega
  exact congrFun hf (boundedWord q I hw)
end RothschildStein.G3

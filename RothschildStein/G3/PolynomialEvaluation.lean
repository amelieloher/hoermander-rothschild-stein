-- Copyright (c) 2026 Scott Armstrong and Amélie Loher. All rights reserved.
-- Released under Apache 2.0 license as described in the file LICENSE.
module
public import RothschildStein.G3.WordPolynomials
@[expose] public section
noncomputable section
namespace RothschildStein.G3

/-- Substitution of finite word polynomials into an associative finite
coefficient algebra (BB (9.75), p. 468). -/
def polynomialEvaluation {a b s : ℕ} {p : Fin b → ℕ+}
    (X : Fin a → FiniteWordAlgebra b s p) :
    MonoidAlgebra ℝ (FreeMonoid (Fin a)) →ₐ[ℝ] FiniteWordAlgebra b s p :=
  MonoidAlgebra.lift ℝ (FiniteWordAlgebra b s p) (FreeMonoid (Fin a)) (FreeMonoid.lift X)

/-- A substituted word has order at least its number of letters when every
input has positive order (BB p. 468). -/
theorem wordEvaluation_order {a b s : ℕ} {p : Fin b → ℕ+}
    (X : Fin a → FiniteWordAlgebra b s p) (hX : ∀ i, FiniteOrderAtLeast 1 (X i))
    (I : List (Fin a)) : FiniteOrderAtLeast I.length (FreeMonoid.lift X (FreeMonoid.ofList I)) := by
  induction I with
  | nil => exact finiteOrderAtLeast_zero _
  | cons i I ih =>
    rw [FreeMonoid.ofList_cons, map_mul, FreeMonoid.lift_eval_of]
    simpa only [List.length_cons, Nat.add_comm] using finiteOrderAtLeast_mul (hX i) ih

/-- Positive-degree substitution cannot lower the order of a polynomial
(BB (9.75), p. 468). -/
theorem polynomialEvaluation_order {a b s k : ℕ} {p : Fin b → ℕ+}
    (X : Fin a → FiniteWordAlgebra b s p) (hX : ∀ i, FiniteOrderAtLeast 1 (X i))
    (f : MonoidAlgebra ℝ (FreeMonoid (Fin a)))
    (hf : OrderAtLeast (fun _ => 1) k (polynomialSeries a f)) :
    FiniteOrderAtLeast k (polynomialEvaluation X f) := by
  classical
  change FiniteOrderAtLeast k
    (MonoidAlgebra.lift ℝ (FiniteWordAlgebra b s p) (FreeMonoid (Fin a)) (FreeMonoid.lift X) f)
  rw [MonoidAlgebra.lift_apply, Finsupp.sum]
  apply finiteOrderAtLeast_sum _ _
  intro I _
  by_cases hI : k ≤ I.toList.length
  · exact finiteOrderAtLeast_smul (finiteOrderAtLeast_mono (wordEvaluation_order X hX I.toList) hI) _
  · have hz := hf I.toList (by rw [ordinary_weight]; omega)
    rw [polynomialSeries_coeff, FreeMonoid.ofList_toList] at hz
    rw [hz, zero_smul]
    exact finiteOrderAtLeast_zero_element k

/-- Every polynomial invisible through ordinary degree s evaluates to zero
in a cutoff-s algebra under positive-order substitution (BB p. 468). -/
theorem polynomialEvaluation_eq_zero_of_truncate_zero {a b s : ℕ} {p : Fin b → ℕ+}
    (X : Fin a → FiniteWordAlgebra b s p) (hX : ∀ i, FiniteOrderAtLeast 1 (X i))
    (f : MonoidAlgebra ℝ (FreeMonoid (Fin a)))
    (hf : ordinaryTrunc s (polynomialSeries a f) = 0) : polynomialEvaluation X f = 0 := by
  apply eq_zero_of_finiteOrderAtLeast_gt (k := s + 1) ?_ (by omega)
  apply polynomialEvaluation_order X hX f
  intro I hI
  have hlen : I.length ≤ s := by rw [ordinary_weight] at hI; omega
  have h := congrFun hf (boundedWord (fun _ => 1) I (by rw [ordinary_weight]; exact hlen))
  exact h
end RothschildStein.G3

-- Copyright (c) 2026 Scott Armstrong and Amélie Loher. All rights reserved.
-- Released under Apache 2.0 license as described in the file LICENSE.
module
public import RothschildStein.G3.BCHComponents
@[expose] public section
noncomputable section
namespace RothschildStein.G3

/-- A substituted word scales by its number of input leaves under
simultaneous real scaling (BB Lemma 9.70, p. 472). -/
theorem wordEvaluation_smul {a b s : ℕ} {p : Fin b → ℕ+}
    (X : Fin a → FiniteWordAlgebra b s p) (r : ℝ) (I : List (Fin a)) :
    FreeMonoid.lift (fun i => r • X i) (FreeMonoid.ofList I) =
      r ^ I.length • FreeMonoid.lift X (FreeMonoid.ofList I) := by
  induction I with
  | nil => simp
  | cons i I ih =>
    rw [FreeMonoid.ofList_cons, map_mul, map_mul, FreeMonoid.lift_eval_of,
      FreeMonoid.lift_eval_of, ih]
    simp only [List.length_cons, smul_mul_assoc, mul_smul_comm, smul_smul, pow_succ]

/-- Homogeneous degree-n polynomial evaluation scales by r^n
(BB Lemma 9.70, p. 472). -/
theorem polynomialEvaluation_smul_homogeneous {a b s n : ℕ} {p : Fin b → ℕ+}
    (X : Fin a → FiniteWordAlgebra b s p) (f : MonoidAlgebra ℝ (FreeMonoid (Fin a)))
    (hf : Homogeneous (fun _ => 1) n (polynomialSeries a f)) (r : ℝ) :
    polynomialEvaluation (fun i => r • X i) f = r ^ n • polynomialEvaluation X f := by
  classical
  change MonoidAlgebra.lift ℝ _ _ (FreeMonoid.lift (fun i => r • X i)) f =
    r ^ n • MonoidAlgebra.lift ℝ _ _ (FreeMonoid.lift X) f
  rw [MonoidAlgebra.lift_apply, MonoidAlgebra.lift_apply, Finsupp.sum, Finsupp.sum, Finset.smul_sum]
  apply Finset.sum_congr rfl
  intro I _
  by_cases hI : I.toList.length = n
  · have h := wordEvaluation_smul X r I.toList
    rw [FreeMonoid.ofList_toList] at h
    rw [h, hI, smul_comm]
  · have hz := hf I.toList (by rw [ordinary_weight]; exact hI)
    rw [polynomialSeries_coeff, FreeMonoid.ofList_toList] at hz
    rw [hz, zero_smul, zero_smul, smul_zero]

/-- The homogeneous evaluation law also holds over the rational scalar
field, retaining rational Lie-polynomial coefficients (BB pp. 471–474). -/
theorem polynomialEvaluation_rat_smul_homogeneous {a b s n : ℕ} {p : Fin b → ℕ+}
    (X : Fin a → FiniteWordAlgebra b s p) (f : MonoidAlgebra ℝ (FreeMonoid (Fin a)))
    (hf : Homogeneous (fun _ => 1) n (polynomialSeries a f)) (r : ℚ) :
    polynomialEvaluation (fun i => r • X i) f = r ^ n • polynomialEvaluation X f := by
  have he : (fun i => r • X i) = (fun i => (r : ℝ) • X i) := by
    funext i
    simpa only [Rat.cast_id] using ratCast_smul_eq ℚ ℝ r (X i)
  rw [he, polynomialEvaluation_smul_homogeneous X f hf]
  have h := ratCast_smul_eq ℚ ℝ (r ^ n) (polynomialEvaluation X f)
  simpa only [Rat.cast_id, Rat.cast_pow] using h.symm

/-- Universal degree-n BCH components are homogeneous under rational
scaling of any prescribed positive arguments (BB Lemma 9.70, p. 472). -/
theorem evaluatedComponent_rat_smul {b s n : ℕ} {p : Fin b → ℕ+}
    (X : Fin 2 → FiniteWordAlgebra b s p) (hX : ∀ i, FiniteOrderAtLeast 1 (X i))
    (r : ℚ) (hrX : ∀ i, FiniteOrderAtLeast 1 (r • X i)) :
    finiteSubstitutionHom (fun i => r • X i) hrX (universalComponent s n) =
      r ^ n • finiteSubstitutionHom X hX (universalComponent s n) :=
  polynomialEvaluation_rat_smul_homogeneous X _ (universalComponent_polynomial_homogeneous s n) r
end RothschildStein.G3

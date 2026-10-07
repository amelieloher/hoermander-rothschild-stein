-- Copyright (c) 2026 Scott Armstrong and Amélie Loher. All rights reserved.
-- Released under Apache 2.0 license as described in the file LICENSE.
module
public import RothschildStein.G3.AssociativeWordSubstitution
public import RothschildStein.G3.Homogeneity
public import RothschildStein.G3.PolynomialTailOperatorBound
@[expose] public section
noncomputable section
open scoped BigOperators
namespace RothschildStein.G3

/-- Homogeneous polynomial letters preserve every word's assigned
weight under associative substitution (BB Lemma 9.22). -/
theorem associativeWord_homogeneous {a b : ℕ}
    (q : Fin a → ℕ+) (p : Fin b → ℕ+)
    (A : Fin a → MonoidAlgebra ℝ (FreeMonoid (Fin b)))
    (hA : ∀ i, Homogeneous p (q i) (polynomialSeries b (A i))) (I : List (Fin a)) :
    Homogeneous p (wordWeight q I)
      (polynomialSeries b (FreeMonoid.lift A (FreeMonoid.ofList I))) := by
  induction I with
  | nil =>
    intro J hJ
    simp only [FreeMonoid.ofList_nil, map_one]
    change (if J = [] then (1 : ℝ) else 0) = 0
    have hn : J ≠ [] := by intro he; subst J; simp [wordWeight] at hJ
    exact ite_eq_right hn
  | cons i I ih =>
    simp only [FreeMonoid.ofList_cons, map_mul, FreeMonoid.lift_eval_of]
    exact homogeneous_convolution p (hA i) ih

/-- Substitution of a cutoff-s polynomial by weight-homogeneous
inputs creates no terms above s; hence no terms are lost in the target
quotient (BB Lemma 9.22, pp. 413–414). -/
theorem associativeWordSubstitution_finitePolynomial_weight_bound {a b s : ℕ}
    (q : Fin a → ℕ+) (p : Fin b → ℕ+)
    (A : Fin a → MonoidAlgebra ℝ (FreeMonoid (Fin b)))
    (hA : ∀ i, Homogeneous p (q i) (polynomialSeries b (A i)))
    (f : WordCoefficients a s q) (J : List (Fin b)) (hJ : s < wordWeight p J) :
    polynomialSeries b (associativeWordSubstitution A (finitePolynomial f)) J = 0 := by
  simp only [finitePolynomial, map_sum, associativeWordSubstitution, MonoidAlgebra.lift_single, map_smul]
  change seriesCoefficientLinear J (∑ I : BoundedWord a s q,
    f I • polynomialSeries b (FreeMonoid.lift A (FreeMonoid.ofList I.val))) = 0
  rw [map_sum]
  apply Finset.sum_eq_zero
  intro I _
  change f I * polynomialSeries b (FreeMonoid.lift A (FreeMonoid.ofList I.val)) J = 0
  rw [associativeWord_homogeneous q p A hA I.val J
    (by have hi : wordWeight q I.val ≤ s := boundedWord_weight I; omega), mul_zero]
end RothschildStein.G3

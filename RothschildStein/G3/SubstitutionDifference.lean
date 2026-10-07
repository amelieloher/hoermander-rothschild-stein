-- Copyright (c) 2026 Scott Armstrong and Amélie Loher. All rights reserved.
-- Released under Apache 2.0 license as described in the file LICENSE.
module
public import RothschildStein.G3.PolynomialHomogeneity
public import Mathlib.Tactic.Abel
@[expose] public section
noncomputable section
namespace RothschildStein.G3

/-- Changing positive inputs by order-two terms changes an m-letter
word only at order at least m+1 (BB Lemma 9.70, p. 472). -/
theorem wordEvaluation_sub_order {a b s : ℕ} {p : Fin b → ℕ+}
    (X Y : Fin a → FiniteWordAlgebra b s p)
    (hX : ∀ i, FiniteOrderAtLeast 1 (X i)) (hY : ∀ i, FiniteOrderAtLeast 1 (Y i))
    (hd : ∀ i, FiniteOrderAtLeast 2 (X i - Y i)) (I : List (Fin a)) :
    FiniteOrderAtLeast (I.length + 1)
      (FreeMonoid.lift X (FreeMonoid.ofList I) - FreeMonoid.lift Y (FreeMonoid.ofList I)) := by
  induction I with
  | nil =>
    simp only [FreeMonoid.ofList_nil, map_one, sub_self, List.length_nil, zero_add]
    exact finiteOrderAtLeast_zero_element 1
  | cons i I ih =>
    rw [FreeMonoid.ofList_cons, map_mul, map_mul, FreeMonoid.lift_eval_of, FreeMonoid.lift_eval_of]
    have he : X i * FreeMonoid.lift X (FreeMonoid.ofList I) -
        Y i * FreeMonoid.lift Y (FreeMonoid.ofList I) =
      (X i - Y i) * FreeMonoid.lift X (FreeMonoid.ofList I) +
        Y i * (FreeMonoid.lift X (FreeMonoid.ofList I) - FreeMonoid.lift Y (FreeMonoid.ofList I)) := by
      rw [sub_mul, mul_sub]
      abel
    rw [he]
    apply finiteOrderAtLeast_add
    · simpa only [List.length_cons, Nat.add_comm, Nat.add_left_comm, Nat.add_assoc] using
        finiteOrderAtLeast_mul (hd i) (wordEvaluation_order X hX I)
    · simpa only [List.length_cons, Nat.add_comm, Nat.add_left_comm, Nat.add_assoc] using
        finiteOrderAtLeast_mul (hY i) ih

/-- A degree-n polynomial is insensitive through order n to order-two
changes of its positive inputs (BB Lemma 9.70 and coefficient comparison (9.80),
p. 472). -/
theorem polynomialEvaluation_sub_order {a b s n : ℕ} {p : Fin b → ℕ+}
    (X Y : Fin a → FiniteWordAlgebra b s p)
    (hX : ∀ i, FiniteOrderAtLeast 1 (X i)) (hY : ∀ i, FiniteOrderAtLeast 1 (Y i))
    (hd : ∀ i, FiniteOrderAtLeast 2 (X i - Y i))
    (f : MonoidAlgebra ℝ (FreeMonoid (Fin a)))
    (hf : Homogeneous (fun _ => 1) n (polynomialSeries a f)) :
    FiniteOrderAtLeast (n + 1) (polynomialEvaluation X f - polynomialEvaluation Y f) := by
  classical
  change FiniteOrderAtLeast (n + 1)
    (MonoidAlgebra.lift ℝ _ _ (FreeMonoid.lift X) f -
      MonoidAlgebra.lift ℝ _ _ (FreeMonoid.lift Y) f)
  rw [MonoidAlgebra.lift_apply, MonoidAlgebra.lift_apply, Finsupp.sum, Finsupp.sum,
    ← Finset.sum_sub_distrib]
  apply finiteOrderAtLeast_sum _ _
  intro I _
  by_cases hI : I.toList.length = n
  · rw [← smul_sub]
    exact finiteOrderAtLeast_smul (by simpa only [hI, FreeMonoid.ofList_toList] using wordEvaluation_sub_order X Y hX hY hd I.toList) _
  · have hz := hf I.toList (by rw [ordinary_weight]; exact hI)
    rw [polynomialSeries_coeff, FreeMonoid.ofList_toList] at hz
    rw [hz, zero_smul, zero_smul, sub_self]
    exact finiteOrderAtLeast_zero_element (n + 1)

/-- In a cutoff-n quotient, the evaluated top BCH component depends
only on the order-one part of each input (BB (9.80), p. 472). -/
theorem evaluatedTopComponent_eq_of_sub_order_two {b n : ℕ} {p : Fin b → ℕ+}
    (X Y : Fin 2 → FiniteWordAlgebra b n p)
    (hX : ∀ i, FiniteOrderAtLeast 1 (X i)) (hY : ∀ i, FiniteOrderAtLeast 1 (Y i))
    (hd : ∀ i, FiniteOrderAtLeast 2 (X i - Y i)) :
    finiteSubstitutionHom X hX (universalComponent n n) =
      finiteSubstitutionHom Y hY (universalComponent n n) := by
  apply sub_eq_zero.mp
  exact eq_zero_of_finiteOrderAtLeast_gt
    (polynomialEvaluation_sub_order X Y hX hY hd _ (universalComponent_polynomial_homogeneous n n))
      (by omega)
end RothschildStein.G3

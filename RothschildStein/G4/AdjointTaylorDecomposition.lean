-- Copyright (c) 2026 Scott Armstrong and Amélie Loher. All rights reserved.
-- Released under Apache 2.0 license as described in the file LICENSE.
module

public import RothschildStein.G4.AdjointTaylorCorrections

@[expose] public section
set_option autoImplicit false
set_option relaxedAutoImplicit false
noncomputable section
open scoped BigOperators

namespace RothschildStein.G4

/-- Removing the zero-order field from the retained Taylor sum
leaves exactly the positive-order adjoint correction (BB pp. 443–444). -/
theorem adjoint_taylor_polynomial_sub_zero {n : ℕ}
    (W Y : (Fin n → ℝ) → (Fin n → ℝ)) (q : ℕ) (x : Fin n → ℝ) :
    (∑ j ∈ Finset.range (q + 1), ((-1 : ℝ) ^ j / ((j + 1).factorial : ℝ)) •
      ((VectorField.lieBracket ℝ W)^[j] Y) x) - Y x =
      ∑ j : Fin q, ((-1 : ℝ) ^ (j.val + 1) / ((j.val + 2).factorial : ℝ)) •
        ((VectorField.lieBracket ℝ W)^[j.val + 1] Y) x := by
  rw [Fin.sum_univ_eq_sum_range (fun j : ℕ =>
    ((-1 : ℝ) ^ (j + 1) / ((j + 2).factorial : ℝ)) •
      ((VectorField.lieBracket ℝ W)^[j + 1] Y) x) q, Finset.sum_range_succ']
  simp only [pow_zero, zero_add, Nat.factorial_one, Nat.cast_one, div_one,
    Function.iterate_zero, id_eq, one_smul]
  abel

/-- An actual derivative minus its leading field splits into the
finite positive-order correction and the actual derivative remainder. -/
theorem adjoint_taylor_error_decomposition {n : ℕ}
    (D W Y : (Fin n → ℝ) → (Fin n → ℝ)) (q : ℕ) (x : Fin n → ℝ) :
    D x - Y x =
      (∑ j : Fin q, ((-1 : ℝ) ^ (j.val + 1) / ((j.val + 2).factorial : ℝ)) •
        ((VectorField.lieBracket ℝ W)^[j.val + 1] Y) x) +
      (D x - ∑ j ∈ Finset.range (q + 1),
        ((-1 : ℝ) ^ j / ((j + 1).factorial : ℝ)) •
          ((VectorField.lieBracket ℝ W)^[j] Y) x) := by
  rw [← adjoint_taylor_polynomial_sub_zero W Y q x]
  abel

end RothschildStein.G4

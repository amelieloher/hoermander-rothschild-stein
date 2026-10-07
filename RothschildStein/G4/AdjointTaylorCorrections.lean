-- Copyright (c) 2026 Scott Armstrong and Amélie Loher. All rights reserved.
-- Released under Apache 2.0 license as described in the file LICENSE.
module

public import RothschildStein.G4.AdjointFrameExpansion

@[expose] public section
set_option autoImplicit false
set_option relaxedAutoImplicit false
noncomputable section
open Set
open scoped BigOperators

namespace RothschildStein.G4

/-- The positive-order adjoint correction has the exact sum of
its Cramer coordinates, with no regularity assumption needed for this
finite linear algebra step (BB pp. 443–444). -/
theorem adjoint_taylor_correction_frameCoefficient {ι : Type*} {n : ℕ}
    (Z : ι → (Fin n → ℝ) → (Fin n → ℝ)) (B : Fin n → ι)
    (W Y : (Fin n → ℝ) → (Fin n → ℝ)) (q : ℕ) (α : Fin q → ℝ)
    (i : Fin n) (x : Fin n → ℝ) :
    frameCoefficient Z B
      (fun y => ∑ j : Fin q, α j • ((VectorField.lieBracket ℝ W)^[j.val + 1] Y) y) i x =
      ∑ j : Fin q, α j *
        frameCoefficient Z B ((VectorField.lieBracket ℝ W)^[j.val + 1] Y) i x :=
  frameCoefficient_external_linear_combination Z B _ _ _ i x rfl

/-- Summing the positive-order adjoint bounds preserves the common
signed output radius weight and every coefficient budget. -/
theorem adjoint_taylor_correction_frameCoefficient_le {ι : Type*} {n : ℕ}
    (Z : ι → (Fin n → ℝ) → (Fin n → ℝ)) (B : Fin n → ι)
    (W Y : (Fin n → ℝ) → (Fin n → ℝ)) (q : ℕ) (α : Fin q → ℝ)
    (i : Fin n) (x : Fin n → ℝ) (c : Fin q → ℝ) {e r : ℝ} {p : ℤ}
    (hbound : ∀ j : Fin q,
      |frameCoefficient Z B ((VectorField.lieBracket ℝ W)^[j.val + 1] Y) i x| ≤
        c j * e ^ (j.val + 1) * r ^ p) :
    |frameCoefficient Z B
      (fun y => ∑ j : Fin q, α j • ((VectorField.lieBracket ℝ W)^[j.val + 1] Y) y) i x| ≤
      (∑ j : Fin q, |α j| * c j * e ^ (j.val + 1)) * r ^ p := by
  rw [adjoint_taylor_correction_frameCoefficient]
  apply (Finset.abs_sum_le_sum_abs _ _).trans
  rw [Finset.sum_mul]
  apply Finset.sum_le_sum
  intro j hj
  rw [abs_mul]
  exact (mul_le_mul_of_nonneg_left (hbound j) (abs_nonneg _)).trans_eq (by ring)

end RothschildStein.G4

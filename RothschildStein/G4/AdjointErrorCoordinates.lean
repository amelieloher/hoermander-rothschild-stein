-- Copyright (c) 2026 Scott Armstrong and Amélie Loher. All rights reserved.
-- Released under Apache 2.0 license as described in the file LICENSE.
module

public import RothschildStein.G4.AdjointTaylorDecomposition
public import RothschildStein.G4.FrameBounds

@[expose] public section
set_option autoImplicit false
set_option relaxedAutoImplicit false
noncomputable section
open scoped BigOperators

namespace RothschildStein.G4

/-- Cramer coordinates add exactly, including at singular frames
where the totalized quotient convention is used. -/
theorem frameCoefficient_add_fields {ι : Type*} {n : ℕ}
    (Z : ι → (Fin n → ℝ) → (Fin n → ℝ)) (B : Fin n → ι)
    (V W : (Fin n → ℝ) → (Fin n → ℝ)) (i : Fin n) (x : Fin n → ℝ) :
    frameCoefficient Z B (fun y => V y + W y) i x =
      frameCoefficient Z B V i x + frameCoefficient Z B W i x := by
  rw [frameCoefficient_coordinates, frameCoefficient_coordinates Z B V,
    frameCoefficient_coordinates Z B W]
  simp only [Pi.add_apply, add_mul, Finset.sum_add_distrib]

/-- The derivative error has exactly the finite-correction and
actual-remainder frame coordinates (BB Lemma 9.49, p. 444). -/
theorem adjoint_taylor_error_frameCoefficient {ι : Type*} {n : ℕ}
    (Z : ι → (Fin n → ℝ) → (Fin n → ℝ)) (B : Fin n → ι)
    (D W Y : (Fin n → ℝ) → (Fin n → ℝ)) (q : ℕ) (i : Fin n) (x : Fin n → ℝ) :
    frameCoefficient Z B (fun y => D y - Y y) i x =
      frameCoefficient Z B
        (fun y => ∑ j : Fin q, ((-1 : ℝ) ^ (j.val + 1) / ((j.val + 2).factorial : ℝ)) •
          ((VectorField.lieBracket ℝ W)^[j.val + 1] Y) y) i x +
      frameCoefficient Z B
        (fun y => D y - ∑ j ∈ Finset.range (q + 1),
          ((-1 : ℝ) ^ j / ((j + 1).factorial : ℝ)) •
            ((VectorField.lieBracket ℝ W)^[j] Y) y) i x := by
  have he : (fun y => D y - Y y) = fun y =>
      (∑ j : Fin q, ((-1 : ℝ) ^ (j.val + 1) / ((j.val + 2).factorial : ℝ)) •
        ((VectorField.lieBracket ℝ W)^[j.val + 1] Y) y) +
      (D y - ∑ j ∈ Finset.range (q + 1),
        ((-1 : ℝ) ^ j / ((j + 1).factorial : ℝ)) •
          ((VectorField.lieBracket ℝ W)^[j] Y) y) := by
    funext y
    exact adjoint_taylor_error_decomposition D W Y q y
  rw [he, frameCoefficient_add_fields]

end RothschildStein.G4

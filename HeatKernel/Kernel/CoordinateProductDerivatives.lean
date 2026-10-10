-- Copyright (c) 2026 Scott Armstrong and Amélie Loher. All rights reserved.
-- Released under Apache 2.0 license as described in the file LICENSE.
module

public import HeatKernel.Kernel.CoordinateDerivatives
public import Mathlib.Analysis.Calculus.ContDiff.Operations

/-! # Product derivatives in time-space coordinates

The time-space linear equivalence carries the unit time vector and lifted
spatial fields to the corresponding product-space vectors.
-/

@[expose] public section

noncomputable section

open RothschildStein

namespace HeatKernel

/-- The coordinate equivalence sends the unit time inclusion to the unit product time vector. -/
theorem timeSpaceCoordinates_time_vector {n : ℕ} :
    timeSpaceCoordinates n (leftCoordinateInclusion 1 n (fun _ => 1)) =
      (1, (0 : Fin n → ℝ)) := by
  rw [← timeSpaceCoordinates_symm_one_zero, ContinuousLinearEquiv.apply_symm_apply]

/-- The coordinate equivalence sends a spatial inclusion to the corresponding product vector. -/
theorem timeSpaceCoordinates_spatial_vector {n : ℕ} (v : Fin n → ℝ) :
    timeSpaceCoordinates n (rightCoordinateInclusion 1 n v) = (0, v) := by
  rw [← timeSpaceCoordinates_symm_zero_left, ContinuousLinearEquiv.apply_symm_apply]

/-- The differential of a function pulled back to coordinates is its product differential. -/
theorem fderiv_comp_timeSpaceCoordinates {n : ℕ}
    (f : ℝ × (Fin n → ℝ) → ℝ) (z w : Fin (1 + n) → ℝ)
    (hf : DifferentiableAt ℝ f (timeSpaceCoordinates n z)) :
    fderiv ℝ (fun a => f (timeSpaceCoordinates n a)) z w =
      fderiv ℝ f (timeSpaceCoordinates n z) (timeSpaceCoordinates n w) := by
  have h := hf.hasFDerivAt.comp z (timeSpaceCoordinates n).hasFDerivAt
  exact congrArg (fun L : (Fin (1 + n) → ℝ) →L[ℝ] ℝ => L w) h.fderiv

/-- The time differential of a coordinate pullback equals the product time differential. -/
theorem fderiv_time_comp_timeSpaceCoordinates {n : ℕ}
    (f : ℝ × (Fin n → ℝ) → ℝ) (z : Fin (1 + n) → ℝ)
    (hf : DifferentiableAt ℝ f (timeSpaceCoordinates n z)) :
    fderiv ℝ (fun a => f (timeSpaceCoordinates n a)) z
        (leftCoordinateInclusion 1 n (fun _ => 1)) =
      fderiv ℝ f (timeSpaceCoordinates n z) (1, 0) := by
  rw [fderiv_comp_timeSpaceCoordinates f _ _ hf, timeSpaceCoordinates_time_vector]

/-- A lifted field differentiates a coordinate pullback in its product spatial direction. -/
theorem fieldDerivative_comp_timeSpaceCoordinates {n : ℕ}
    (V : (Fin n → ℝ) → Fin n → ℝ)
    (f : ℝ × (Fin n → ℝ) → ℝ) (z : Fin (1 + n) → ℝ)
    (hf : DifferentiableAt ℝ f (timeSpaceCoordinates n z)) :
    fieldDerivative (liftRightField 1 V) (fun a => f (timeSpaceCoordinates n a)) z =
      fderiv ℝ f (timeSpaceCoordinates n z) (0, V (timeSpaceCoordinates n z).2) := by
  change fderiv ℝ (fun a => f (timeSpaceCoordinates n a)) z
    (rightCoordinateInclusion 1 n (V (rightCoordinateProjection 1 n z))) = _
  rw [fderiv_comp_timeSpaceCoordinates f _ _ hf, timeSpaceCoordinates_spatial_vector]
  rfl

end HeatKernel

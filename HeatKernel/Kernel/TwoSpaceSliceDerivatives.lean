-- Copyright (c) 2026 Scott Armstrong and Amélie Loher. All rights reserved.
-- Released under Apache 2.0 license as described in the file LICENSE.
module

public import HeatKernel.Kernel.TwoSpaceTestSlices
public import HeatKernel.Kernel.CoordinateDerivatives
public import Mathlib.Analysis.Calculus.FDeriv.Prod
public import RothschildStein.S.Transposes

/-! # Derivatives of two-space test slices

The linear part of endpoint insertion carries time and spatial directions to
the corresponding full coordinate directions. The chain rule therefore
identifies the section test operator with its two-space counterpart.
-/

@[expose] public section

noncomputable section

namespace HeatKernel

/-- The linear part of insertion of a fixed second spatial endpoint. -/
def twoSpaceSliceLinear (n : ℕ) :
    (Fin (1 + n) → ℝ) →L[ℝ] (Fin (1 + (n + n)) → ℝ) :=
  (timeTwoSpaceCoordinatesAssoc n).symm.toContinuousLinearMap.comp
    ((timeSpaceCoordinates n).toContinuousLinearMap.prod 0)

/-- Endpoint insertion has derivative equal to its linear part. -/
theorem hasFDerivAt_twoSpaceCoordinateSlice {n : ℕ} (y : Fin n → ℝ)
    (z : Fin (1 + n) → ℝ) :
    HasFDerivAt (twoSpaceCoordinateSlice y) (twoSpaceSliceLinear n) z := by
  exact (timeTwoSpaceCoordinatesAssoc n).symm.hasFDerivAt.comp z
    ((timeSpaceCoordinates n).hasFDerivAt.prodMk (hasFDerivAt_const y z))

/-- The linear part of endpoint insertion preserves the unit time direction. -/
theorem twoSpaceSliceLinear_time (n : ℕ) :
    twoSpaceSliceLinear n (leftCoordinateInclusion 1 n (fun _ => 1)) =
      leftCoordinateInclusion 1 (n + n) (fun _ => 1) := by
  simp [twoSpaceSliceLinear, timeTwoSpaceCoordinatesAssoc, timeTwoSpaceCoordinates,
    timeSpaceCoordinates, leftCoordinateInclusion]
  rfl

/-- The linear part inserts a spatial vector into the first spatial block. -/
theorem twoSpaceSliceLinear_spatial {n : ℕ} (w : Fin n → ℝ) :
    twoSpaceSliceLinear n (rightCoordinateInclusion 1 n w) =
      rightCoordinateInclusion 1 (n + n) (leftCoordinateInclusion n n w) := by
  simp [twoSpaceSliceLinear, timeTwoSpaceCoordinatesAssoc, timeTwoSpaceCoordinates,
    timeSpaceCoordinates, leftCoordinateInclusion, rightCoordinateInclusion]
  rfl

/-- The chain rule identifies directional derivatives of a section test. -/
theorem fderiv_twoSpace_test_slice {n : ℕ}
    (φ : (Fin (1 + (n + n)) → ℝ) → ℝ) (y : Fin n → ℝ)
    (z w : Fin (1 + n) → ℝ) (hφ : DifferentiableAt ℝ φ (twoSpaceCoordinateSlice y z)) :
    fderiv ℝ (φ ∘ twoSpaceCoordinateSlice y) z w =
      fderiv ℝ φ (twoSpaceCoordinateSlice y z) (twoSpaceSliceLinear n w) := by
  have h := hφ.hasFDerivAt.comp z (hasFDerivAt_twoSpaceCoordinateSlice y z)
  rw [h.fderiv]
  rfl

/-- Section time derivatives are the full two-space time derivatives. -/
theorem fderiv_time_twoSpace_test_slice {n : ℕ}
    (φ : (Fin (1 + (n + n)) → ℝ) → ℝ) (y : Fin n → ℝ)
    (z : Fin (1 + n) → ℝ) (hφ : DifferentiableAt ℝ φ (twoSpaceCoordinateSlice y z)) :
    fderiv ℝ (φ ∘ twoSpaceCoordinateSlice y) z (leftCoordinateInclusion 1 n (fun _ => 1)) =
      fderiv ℝ φ (twoSpaceCoordinateSlice y z)
        (leftCoordinateInclusion 1 (n + n) (fun _ => 1)) := by
  rw [fderiv_twoSpace_test_slice φ y z _ hφ, twoSpaceSliceLinear_time]

/-- The first spatial block of an inserted endpoint is the original spatial coordinate. -/
theorem left_block_projection_twoSpaceCoordinateSlice {n : ℕ}
    (y : Fin n → ℝ) (z : Fin (1 + n) → ℝ) :
    leftCoordinateProjection n n (rightCoordinateProjection 1 (n + n)
      (twoSpaceCoordinateSlice y z)) = rightCoordinateProjection 1 n z := by
  change (timeTwoSpaceCoordinatesAssoc n
    ((timeTwoSpaceCoordinatesAssoc n).symm (timeSpaceCoordinates n z, y))).1.2 =
      (timeSpaceCoordinates n z).2
  rw [ContinuousLinearEquiv.apply_symm_apply]

/-- The linear part of insertion carries a section field to the first full spatial block. -/
theorem twoSpaceSliceLinear_liftRightField {n : ℕ}
    (X : (Fin n → ℝ) → Fin n → ℝ) (y : Fin n → ℝ) (z : Fin (1 + n) → ℝ) :
    twoSpaceSliceLinear n (liftRightField 1 X z) =
      liftRightField 1 (liftLeftField n X) (twoSpaceCoordinateSlice y z) := by
  simp only [liftRightField, liftLeftField, twoSpaceSliceLinear_spatial,
    left_block_projection_twoSpaceCoordinateSlice]

/-- A section field derivative agrees with the first-block field derivative of the full test. -/
theorem fieldDerivative_twoSpace_test_slice {n : ℕ}
    (X : (Fin n → ℝ) → Fin n → ℝ) (φ : (Fin (1 + (n + n)) → ℝ) → ℝ)
    (y : Fin n → ℝ) (z : Fin (1 + n) → ℝ)
    (hφ : DifferentiableAt ℝ φ (twoSpaceCoordinateSlice y z)) :
    RothschildStein.fieldDerivative (liftRightField 1 X) (φ ∘ twoSpaceCoordinateSlice y) z =
      RothschildStein.fieldDerivative (liftRightField 1 (liftLeftField n X)) φ
        (twoSpaceCoordinateSlice y z) := by
  unfold RothschildStein.fieldDerivative
  rw [fderiv_twoSpace_test_slice φ y z _ hφ, twoSpaceSliceLinear_liftRightField]

/-- The iterated section field derivative agrees with the full first-block square. -/
theorem fieldDerivative_sq_twoSpace_test_slice {n : ℕ}
    (X : (Fin n → ℝ) → Fin n → ℝ) (hX : ContDiff ℝ (⊤ : ℕ∞) X)
    (φ : (Fin (1 + (n + n)) → ℝ) → ℝ) (hφ : ContDiff ℝ (⊤ : ℕ∞) φ)
    (y : Fin n → ℝ) (z : Fin (1 + n) → ℝ) :
    RothschildStein.fieldDerivative (liftRightField 1 X)
      (RothschildStein.fieldDerivative (liftRightField 1 X) (φ ∘ twoSpaceCoordinateSlice y)) z =
      RothschildStein.fieldDerivative (liftRightField 1 (liftLeftField n X))
        (RothschildStein.fieldDerivative (liftRightField 1 (liftLeftField n X)) φ)
          (twoSpaceCoordinateSlice y z) := by
  have heq : RothschildStein.fieldDerivative (liftRightField 1 X) (φ ∘ twoSpaceCoordinateSlice y) =
      (RothschildStein.fieldDerivative (liftRightField 1 (liftLeftField n X)) φ) ∘
        twoSpaceCoordinateSlice y :=
    funext fun w => fieldDerivative_twoSpace_test_slice X φ y w
      (hφ.differentiable (by simp)).differentiableAt
  rw [heq]
  have hs := RothschildStein.S.contDiffOn_fieldDerivative
    (⟨Set.univ, isOpen_univ⟩ : TopologicalSpace.Opens (Fin (1 + (n + n)) → ℝ))
    (liftRightField 1 (liftLeftField n X)) φ
    ((hX.liftLeftField n).liftRightField 1).contDiffOn hφ.contDiffOn
  exact fieldDerivative_twoSpace_test_slice X _ y z
    ((contDiffOn_univ.mp hs).differentiable (by simp)).differentiableAt

end HeatKernel

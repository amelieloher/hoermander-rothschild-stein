-- Copyright (c) 2026 Scott Armstrong and Amélie Loher. All rights reserved.
-- Released under Apache 2.0 license as described in the file LICENSE.
module

public import HeatKernel.Kernel.TwoSpaceSwap
public import RothschildStein.S.Transposes

/-! # Differential tests under spatial block exchange

Spatial exchange retains the time direction and carries the first lifted field
to the second. The chain rule transports the corresponding sum of squares.
-/

@[expose] public section

noncomputable section

namespace HeatKernel

open RothschildStein

/-- Spatial exchange preserves the unit time vector. -/
theorem twoSpaceSwap_time_vector (n : ℕ) :
    twoSpaceSwap n (leftCoordinateInclusion 1 (n + n) (fun _ => 1)) =
      leftCoordinateInclusion 1 (n + n) (fun _ => 1) := by
  simp [twoSpaceSwap, timeTwoSpaceCoordinates, timeSpaceCoordinates, leftCoordinateInclusion]
  rfl

/-- Spatial exchange carries a first-block spatial vector into the second block. -/
theorem twoSpaceSwap_first_vector {n : ℕ} (w : Fin n → ℝ) :
    twoSpaceSwap n (rightCoordinateInclusion 1 (n + n) (leftCoordinateInclusion n n w)) =
      rightCoordinateInclusion 1 (n + n) (rightCoordinateInclusion n n w) := by
  simp [twoSpaceSwap, timeTwoSpaceCoordinates, timeSpaceCoordinates,
    leftCoordinateInclusion, rightCoordinateInclusion]
  rfl

/-- After exchange, the second spatial projection is the original first projection. -/
theorem second_projection_twoSpaceSwap {n : ℕ} (z : Fin (1 + (n + n)) → ℝ) :
    rightCoordinateProjection n n (rightCoordinateProjection 1 (n + n) (twoSpaceSwap n z)) =
      leftCoordinateProjection n n (rightCoordinateProjection 1 (n + n) z) := by
  change (timeTwoSpaceCoordinates n (twoSpaceSwap n z)).2.2 = (timeTwoSpaceCoordinates n z).2.1
  rw [timeTwoSpaceCoordinates_twoSpaceSwap]

/-- Spatial exchange carries the first lifted field to the second lifted field. -/
theorem twoSpaceSwap_first_field {n : ℕ} (X : (Fin n → ℝ) → Fin n → ℝ)
    (z : Fin (1 + (n + n)) → ℝ) :
    twoSpaceSwap n (liftRightField 1 (liftLeftField n X) z) =
      liftRightField 1 (liftRightField n X) (twoSpaceSwap n z) := by
  simp only [liftRightField, liftLeftField, twoSpaceSwap_first_vector, second_projection_twoSpaceSwap]

/-- Directional derivatives transform by the linear spatial exchange. -/
theorem fderiv_comp_twoSpaceSwap {n : ℕ}
    (φ : (Fin (1 + (n + n)) → ℝ) → ℝ) (z w : Fin (1 + (n + n)) → ℝ)
    (hφ : DifferentiableAt ℝ φ (twoSpaceSwap n z)) :
    fderiv ℝ (φ ∘ twoSpaceSwap n) z w = fderiv ℝ φ (twoSpaceSwap n z) (twoSpaceSwap n w) := by
  rw [(hφ.hasFDerivAt.comp z (twoSpaceSwap n).hasFDerivAt).fderiv]
  rfl

/-- Time differentiation commutes with spatial block exchange. -/
theorem fderiv_time_comp_twoSpaceSwap {n : ℕ}
    (φ : (Fin (1 + (n + n)) → ℝ) → ℝ) (z : Fin (1 + (n + n)) → ℝ)
    (hφ : DifferentiableAt ℝ φ (twoSpaceSwap n z)) :
    fderiv ℝ (φ ∘ twoSpaceSwap n) z (leftCoordinateInclusion 1 (n + n) (fun _ => 1)) =
      fderiv ℝ φ (twoSpaceSwap n z) (leftCoordinateInclusion 1 (n + n) (fun _ => 1)) := by
  rw [fderiv_comp_twoSpaceSwap φ z _ hφ, twoSpaceSwap_time_vector]

/-- The first field derivative of a pulled-back test is its second field derivative after exchange. -/
theorem fieldDerivative_first_comp_twoSpaceSwap {n : ℕ}
    (X : (Fin n → ℝ) → Fin n → ℝ) (φ : (Fin (1 + (n + n)) → ℝ) → ℝ)
    (z : Fin (1 + (n + n)) → ℝ) (hφ : DifferentiableAt ℝ φ (twoSpaceSwap n z)) :
    fieldDerivative (liftRightField 1 (liftLeftField n X)) (φ ∘ twoSpaceSwap n) z =
      fieldDerivative (liftRightField 1 (liftRightField n X)) φ (twoSpaceSwap n z) := by
  unfold fieldDerivative
  rw [fderiv_comp_twoSpaceSwap φ z _ hφ, twoSpaceSwap_first_field]

/-- The first field square of a pulled-back test is its second field square after exchange. -/
theorem fieldDerivative_sq_first_comp_twoSpaceSwap {n : ℕ}
    (X : (Fin n → ℝ) → Fin n → ℝ) (hX : ContDiff ℝ (⊤ : ℕ∞) X)
    (φ : (Fin (1 + (n + n)) → ℝ) → ℝ) (hφ : ContDiff ℝ (⊤ : ℕ∞) φ)
    (z : Fin (1 + (n + n)) → ℝ) :
    fieldDerivative (liftRightField 1 (liftLeftField n X))
      (fieldDerivative (liftRightField 1 (liftLeftField n X)) (φ ∘ twoSpaceSwap n)) z =
      fieldDerivative (liftRightField 1 (liftRightField n X))
        (fieldDerivative (liftRightField 1 (liftRightField n X)) φ) (twoSpaceSwap n z) := by
  have heq : fieldDerivative (liftRightField 1 (liftLeftField n X)) (φ ∘ twoSpaceSwap n) =
      (fieldDerivative (liftRightField 1 (liftRightField n X)) φ) ∘ twoSpaceSwap n :=
    funext fun w => fieldDerivative_first_comp_twoSpaceSwap X φ w
      (hφ.differentiable (by simp)).differentiableAt
  rw [heq]
  have hs := S.contDiffOn_fieldDerivative
    (⟨Set.univ, isOpen_univ⟩ : TopologicalSpace.Opens (Fin (1 + (n + n)) → ℝ))
    (liftRightField 1 (liftRightField n X)) φ
    ((hX.liftRightField n).liftRightField 1).contDiffOn hφ.contDiffOn
  exact fieldDerivative_first_comp_twoSpaceSwap X _ z
    ((contDiffOn_univ.mp hs).differentiable (by simp)).differentiableAt

end HeatKernel

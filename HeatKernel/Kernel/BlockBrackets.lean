-- Copyright (c) 2026 Scott Armstrong and Amélie Loher. All rights reserved.
-- Released under Apache 2.0 license as described in the file LICENSE.
module

public import HeatKernel.Kernel.Coordinates
public import RothschildStein.G1.BracketAlgebra

/-! # Brackets of fields on coordinate blocks

Coordinate inclusions and projections preserve brackets within each block.
-/

@[expose] public section

noncomputable section

namespace HeatKernel

open RothschildStein

@[simp] theorem leftCoordinateProjection_leftCoordinateInclusion (m n : ℕ) (v : Fin m → ℝ) :
    leftCoordinateProjection m n (leftCoordinateInclusion m n v) = v := by
  ext i
  simp

@[simp] theorem rightCoordinateProjection_rightCoordinateInclusion (m n : ℕ) (v : Fin n → ℝ) :
    rightCoordinateProjection m n (rightCoordinateInclusion m n v) = v := by
  ext i
  simp

/-- Every vector is the sum of its two coordinate inclusions. -/
theorem coordinateInclusions_add (m n : ℕ) (v : Fin (m + n) → ℝ) :
    leftCoordinateInclusion m n (leftCoordinateProjection m n v) +
      rightCoordinateInclusion m n (rightCoordinateProjection m n v) = v := by
  ext i
  refine Fin.addCases (fun j => ?_) (fun j => ?_) i <;> simp

/-- The bracket of two differentiable fields commutes with a linear retraction lift. -/
theorem lieBracket_linear_lift {E F : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    [NormedAddCommGroup F] [NormedSpace ℝ F] (I : F →L[ℝ] E) (P : E →L[ℝ] F)
    (hPI : ∀ v, P (I v) = v) (X Y : F → F) (z : E)
    (hX : DifferentiableAt ℝ X (P z)) (hY : DifferentiableAt ℝ Y (P z)) :
    VectorField.lieBracket ℝ (fun x => I (X (P x))) (fun x => I (Y (P x))) z =
      I (VectorField.lieBracket ℝ X Y (P z)) := by
  have hdX := I.hasFDerivAt.comp z (hX.hasFDerivAt.comp z P.hasFDerivAt)
  have hdY := I.hasFDerivAt.comp z (hY.hasFDerivAt.comp z P.hasFDerivAt)
  unfold VectorField.lieBracket
  change (fderiv ℝ (I ∘ Y ∘ P) z) (I (X (P z))) -
    (fderiv ℝ (I ∘ X ∘ P) z) (I (Y (P z))) = _
  rw [hdX.fderiv, hdY.fderiv]
  simp only [ContinuousLinearMap.comp_apply, hPI, map_sub]

/-- Brackets within the left coordinate block are lifts of the original brackets. -/
theorem lieBracket_liftLeftField {m : ℕ} (n : ℕ)
    (X Y : (Fin m → ℝ) → Fin m → ℝ)
    (hX : Differentiable ℝ X) (hY : Differentiable ℝ Y) :
    VectorField.lieBracket ℝ (liftLeftField n X) (liftLeftField n Y) =
      liftLeftField n (VectorField.lieBracket ℝ X Y) := by
  funext z
  exact lieBracket_linear_lift _ _ (leftCoordinateProjection_leftCoordinateInclusion m n)
    X Y z (hX _) (hY _)

/-- Brackets within the right coordinate block are lifts of the original brackets. -/
theorem lieBracket_liftRightField (m : ℕ) {n : ℕ}
    (X Y : (Fin n → ℝ) → Fin n → ℝ)
    (hX : Differentiable ℝ X) (hY : Differentiable ℝ Y) :
    VectorField.lieBracket ℝ (liftRightField m X) (liftRightField m Y) =
      liftRightField m (VectorField.lieBracket ℝ X Y) := by
  funext z
  exact lieBracket_linear_lift _ _ (rightCoordinateProjection_rightCoordinateInclusion m n)
    X Y z (hX _) (hY _)

/-- Smooth generators give smooth right-nested word brackets. -/
theorem contDiff_wordBracket {q n : ℕ} (X : Fin q → (Fin n → ℝ) → Fin n → ℝ)
    (hX : ∀ i, ContDiff ℝ (⊤ : ℕ∞) (X i)) (w : List (Fin q)) :
    ContDiff ℝ (⊤ : ℕ∞) (wordBracket X w) := by
  simpa only [contDiffOn_univ] using
    G1.wordBracket_contDiffOn isOpen_univ X (fun i => (hX i).contDiffOn) w

/-- Word brackets commute with lifting all generators to the left block. -/
theorem wordBracket_liftLeftField {q : ℕ} {m : ℕ} (n : ℕ)
    (X : Fin q → (Fin m → ℝ) → Fin m → ℝ)
    (hX : ∀ i, ContDiff ℝ (⊤ : ℕ∞) (X i)) (w : List (Fin q)) :
    wordBracket (fun i => liftLeftField n (X i)) w = liftLeftField n (wordBracket X w) := by
  induction w with
  | nil =>
      funext x
      simp [wordBracket, liftLeftField]
  | cons i w ih =>
      cases w with
      | nil => rfl
      | cons j w =>
          change VectorField.lieBracket ℝ (liftLeftField n (X i))
            (wordBracket (fun i => liftLeftField n (X i)) (j :: w)) = _
          rw [ih, lieBracket_liftLeftField n (X i) (wordBracket X (j :: w))
            ((hX i).differentiable (by simp))
            ((contDiff_wordBracket X hX (j :: w)).differentiable (by simp))]
          rfl

/-- Word brackets commute with lifting all generators to the right block. -/
theorem wordBracket_liftRightField {q : ℕ} {n : ℕ} (m : ℕ)
    (X : Fin q → (Fin n → ℝ) → Fin n → ℝ)
    (hX : ∀ i, ContDiff ℝ (⊤ : ℕ∞) (X i)) (w : List (Fin q)) :
    wordBracket (fun i => liftRightField m (X i)) w = liftRightField m (wordBracket X w) := by
  induction w with
  | nil =>
      funext x
      simp [wordBracket, liftRightField]
  | cons i w ih =>
      cases w with
      | nil => rfl
      | cons j w =>
          change VectorField.lieBracket ℝ (liftRightField m (X i))
            (wordBracket (fun i => liftRightField m (X i)) (j :: w)) = _
          rw [ih, lieBracket_liftRightField m (X i) (wordBracket X (j :: w))
            ((hX i).differentiable (by simp))
            ((contDiff_wordBracket X hX (j :: w)).differentiable (by simp))]
          rfl

end HeatKernel

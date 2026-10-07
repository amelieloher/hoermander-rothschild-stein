-- Copyright (c) 2026 Scott Armstrong and Amélie Loher. All rights reserved.
-- Released under Apache 2.0 license as described in the file LICENSE.
module

public import RothschildStein.Definitions.FreeAt
public import RothschildStein.G4.Frames
public import Mathlib.LinearAlgebra.Matrix.NonsingularInverse

@[expose] public section
set_option autoImplicit false
set_option relaxedAutoImplicit false
noncomputable section
open scoped BigOperators

namespace RothschildStein.L1

/-- Accumulate a frame's coefficients in the bounded-word
carrier, including repeated frame words. -/
def frameWordCoefficients {a n s : ℕ} {w : Fin a → ℕ+}
    (B : Fin n → BoundedWord a s w) (c : Fin n → ℝ) : BoundedWord a s w → ℝ := by
  classical
  exact fun I => ∑ j, if B j = I then c j else 0

/-- Accumulation retains the entire actual vector combination. -/
theorem frameWordCoefficients_sum {a n s : ℕ} {w : Fin a → ℕ+}
    (X : Fin a → (Fin n → ℝ) → (Fin n → ℝ))
    (B : Fin n → BoundedWord a s w) (c : Fin n → ℝ) (x : Fin n → ℝ) :
    (∑ I, frameWordCoefficients B c I • wordBracket X (boundedWordList I) x) =
      ∑ j, c j • wordBracket X (boundedWordList (B j)) x := by
  classical
  unfold frameWordCoefficients
  simp only [Finset.sum_smul]
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro j hj
  simp [ite_smul]

/-- Freeness (`FreeAt`) makes every frame's linear relations
independent of the evaluation point (BB Proposition 10.35, pp. 514–515). -/
theorem frame_relation_iff_of_FreeAt {a n s : ℕ} {w : Fin a → ℕ+}
    (X : Fin a → (Fin n → ℝ) → (Fin n → ℝ))
    {x y : Fin n → ℝ} (hx : FreeAt w s X x) (hy : FreeAt w s X y)
    (B : Fin n → BoundedWord a s w) (c : Fin n → ℝ) :
    (∑ j, c j • wordBracket X (boundedWordList (B j)) x) = 0 ↔
      (∑ j, c j • wordBracket X (boundedWordList (B j)) y) = 0 := by
  have hh := (hx (frameWordCoefficients B c)).trans (hy (frameWordCoefficients B c)).symm
  simpa only [frameWordCoefficients_sum] using hh

private theorem frameDet_ne_zero_transfer {a n s : ℕ} {w : Fin a → ℕ+}
    (X : Fin a → (Fin n → ℝ) → (Fin n → ℝ))
    {x y : Fin n → ℝ} (hx : FreeAt w s X x) (hy : FreeAt w s X y)
    (B : Fin n → BoundedWord a s w)
    (hdet : G4.frameDet (fun I => wordBracket X (boundedWordList I)) B x ≠ 0) :
    G4.frameDet (fun I => wordBracket X (boundedWordList I)) B y ≠ 0 := by
  classical
  let Z := fun I : BoundedWord a s w => wordBracket X (boundedWordList I)
  have hker : ∀ c : Fin n → ℝ, (G4.frameMatrix Z B x).mulVec c = 0 ↔
      (G4.frameMatrix Z B y).mulVec c = 0 := by
    intro c
    have hh := frame_relation_iff_of_FreeAt X hx hy B c
    have hmul : ∀ z : Fin n → ℝ, (G4.frameMatrix Z B z).mulVec c =
        ∑ j, c j • Z (B j) z := by
      intro z
      ext i
      simp [G4.frameMatrix, Matrix.mulVec, dotProduct, mul_comm]
    rw [hmul x, hmul y]
    exact hh
  have hinj : Function.Injective (G4.frameMatrix Z B x).mulVec :=
    Matrix.mulVec_injective_iff_isUnit.mpr
      ((G4.frameMatrix Z B x).isUnit_iff_isUnit_det.mpr (isUnit_iff_ne_zero.mpr hdet))
  have hinj' : Function.Injective (G4.frameMatrix Z B y).mulVec := by
    intro u v huv
    have hh : (G4.frameMatrix Z B y).mulVec (u - v) = 0 := by
      rw [Matrix.mulVec_sub, huv, sub_self]
    have hh' := (hker (u - v)).mpr hh
    have hz : u - v = 0 := hinj (by simpa only [Matrix.mulVec_zero] using hh')
    exact sub_eq_zero.mp hz
  exact isUnit_iff_ne_zero.mp
    ((G4.frameMatrix Z B y).isUnit_iff_isUnit_det.mp (Matrix.mulVec_injective_iff_isUnit.mp hinj'))

/-- Every candidate frame determinant is either everywhere zero
or nowhere zero on a free patch, directly from `FreeAt`. -/
theorem frameDet_ne_zero_iff_of_FreeAt {a n s : ℕ} {w : Fin a → ℕ+}
    (X : Fin a → (Fin n → ℝ) → (Fin n → ℝ))
    {x y : Fin n → ℝ} (hx : FreeAt w s X x) (hy : FreeAt w s X y)
    (B : Fin n → BoundedWord a s w) :
    G4.frameDet (fun I => wordBracket X (boundedWordList I)) B x ≠ 0 ↔
      G4.frameDet (fun I => wordBracket X (boundedWordList I)) B y ≠ 0 :=
  ⟨frameDet_ne_zero_transfer X hx hy B, frameDet_ne_zero_transfer X hy hx B⟩

end RothschildStein.L1

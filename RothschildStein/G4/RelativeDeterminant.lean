-- Copyright (c) 2026 Scott Armstrong and Amélie Loher. All rights reserved.
-- Released under Apache 2.0 license as described in the file LICENSE.
module

public import RothschildStein.G4.GeneratorProducts

@[expose] public section
set_option autoImplicit false
set_option relaxedAutoImplicit false
noncomputable section
open Set
open scoped BigOperators

namespace RothschildStein.G4

/-- Coordinates of another frame in the selected frame. -/
def frameCoordinateMatrix {ι : Type*} {n : ℕ}
    (Z : ι → (Fin n → ℝ) → (Fin n → ℝ)) (B C : Fin n → ι) (x : Fin n → ℝ) :
    Matrix (Fin n) (Fin n) ℝ :=
  fun i j => frameCoefficient Z B (Z (C j)) i x

/-- Another frame determinant is the original determinant times
the determinant of its actual coordinate matrix (BB Lemma 9.37, p. 429). -/
theorem frameDet_eq_coordinateDet_mul {ι : Type*} {n : ℕ}
    (Z : ι → (Fin n → ℝ) → (Fin n → ℝ)) (B C : Fin n → ι)
    {x : Fin n → ℝ} (hB : frameDet Z B x ≠ 0) :
    frameDet Z C x = (frameCoordinateMatrix Z B C x).det * frameDet Z B x := by
  have hmat : frameMatrix Z C x = frameMatrix Z B x * frameCoordinateMatrix Z B C x := by
    ext k j
    have h := congrFun (frame_representation Z B (Z (C j)) hB) k
    simpa only [frameMatrix, frameCoordinateMatrix, Matrix.mul_apply, Finset.sum_apply,
      Pi.smul_apply, smul_eq_mul, mul_comm] using h
  unfold frameDet
  rw [hmat, Matrix.det_mul, mul_comm]

/-- A term of the coordinate determinant is an `n`-factor
generator with exact frame-weight difference (BB Lemma 9.37, p. 429). -/
theorem coordinateDet_product_isGenerator {ι : Type*} {n : ℕ}
    (Z : ι → (Fin n → ℝ) → (Fin n → ℝ)) (w : ι → ℕ+) (B C : Fin n → ι)
    (σ : Equiv.Perm (Fin n)) :
    IsGenerator Z w B n (frameWeight w B - frameWeight w C)
      (fun x => ∏ j, frameCoefficient Z B (Z (C j)) (σ j) x) := by
  classical
  let M := (Finset.univ : Finset (Fin n)).toList.map (fun j => (σ j, C j))
  have hdef : generatorDeficit w B M = frameWeight w B - frameWeight w C := by
    simp only [generatorDeficit, M, List.map_map, Function.comp_def, Finset.sum_map_toList,
      Finset.sum_sub_distrib, frameWeight]
    rw [Equiv.sum_comp σ (fun i => ((w (B i) : ℕ) : ℤ))]
  refine ⟨M, ?_, hdef.ge, ?_⟩
  · simp only [M, List.length_map, Finset.length_toList, Finset.card_univ, Fintype.card_fin]
    exact le_rfl
  · funext x
    simp only [generatorValue, M, List.map_map, Function.comp_def, Finset.prod_map_toList]

end RothschildStein.G4

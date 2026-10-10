-- Copyright (c) 2026 Scott Armstrong and Amélie Loher. All rights reserved.
-- Released under Apache 2.0 license as described in the file LICENSE.
module

public import HeatKernel.Form.Ellipticity
public import Mathlib.Analysis.Normed.Group.Real
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Ring

import Mathlib.Tactic.Linter

/-! # Entry bounds from symmetric quadratic-form bounds -/

@[expose] public section

noncomputable section

open Set

namespace HeatKernel

private theorem matrixEnergy_single {ι : Type*} [Fintype ι] [DecidableEq ι]
    (a : ι → ι → ℝ) (i : ι) : matrixEnergy a (Pi.single i 1) = a i i := by
  simp [matrixEnergy, Pi.single_apply]

private theorem coordinateNormSq_single {ι : Type*} [Fintype ι] [DecidableEq ι]
    (i : ι) : coordinateNormSq (Pi.single i (1 : ℝ)) = 1 := by
  simp [coordinateNormSq, Pi.single_apply]

private theorem matrixEnergy_add_single {ι : Type*} [Fintype ι] [DecidableEq ι]
    (a : ι → ι → ℝ) (i j : ι) :
    matrixEnergy a (fun k => (Pi.single i (1 : ℝ) : ι → ℝ) k + (Pi.single j (1 : ℝ) : ι → ℝ) k) =
      a i i + a j j + a i j + a j i := by
  simp [matrixEnergy, mul_add, Finset.sum_add_distrib, Pi.single_apply]
  ring

private theorem matrixEnergy_sub_single {ι : Type*} [Fintype ι] [DecidableEq ι]
    (a : ι → ι → ℝ) (i j : ι) :
    matrixEnergy a (fun k => (Pi.single i (1 : ℝ) : ι → ℝ) k - (Pi.single j (1 : ℝ) : ι → ℝ) k) =
      a i i + a j j - a i j - a j i := by
  simp [matrixEnergy, mul_sub, Finset.sum_sub_distrib, Pi.single_apply]
  ring

/-- Every entry of a symmetric nonnegative matrix is bounded by a quadratic upper bound. -/
theorem abs_matrix_entry_le_of_quadratic_bounds {ι : Type*} [Fintype ι] [DecidableEq ι]
    (a : ι → ι → ℝ) {upper : ℝ} (hsym : ∀ i j, a i j = a j i)
    (hpos : ∀ ξ, 0 ≤ matrixEnergy a ξ)
    (hupper : ∀ ξ, matrixEnergy a ξ ≤ upper * coordinateNormSq ξ) (i j : ι) :
    |a i j| ≤ upper := by
  have hdiag : ∀ k, a k k ≤ upper := fun k => by
    simpa only [matrixEnergy_single, coordinateNormSq_single, mul_one] using hupper (Pi.single k 1)
  have hp := hpos (fun k => (Pi.single i (1 : ℝ) : ι → ℝ) k + (Pi.single j (1 : ℝ) : ι → ℝ) k)
  have hm := hpos (fun k => (Pi.single i (1 : ℝ) : ι → ℝ) k - (Pi.single j (1 : ℝ) : ι → ℝ) k)
  rw [matrixEnergy_add_single, hsym j i] at hp
  rw [matrixEnergy_sub_single, hsym j i] at hm
  exact abs_le.mpr ⟨by linarith [hdiag i, hdiag j], by linarith [hdiag i, hdiag j]⟩

/-- A symmetric elliptic matrix has entrywise norm at most its ellipticity upper bound. -/
theorem norm_matrix_entry_le_of_elliptic_bounds {ι : Type*} [Fintype ι] [DecidableEq ι]
    (a : ι → ι → ℝ) {lower upper : ℝ} (hlower : 0 ≤ lower) (hsym : ∀ i j, a i j = a j i)
    (hbound : ∀ ξ, lower * coordinateNormSq ξ ≤ matrixEnergy a ξ ∧
      matrixEnergy a ξ ≤ upper * coordinateNormSq ξ) (i j : ι) : ‖a i j‖ ≤ upper := by
  change |a i j| ≤ upper
  apply abs_matrix_entry_le_of_quadratic_bounds a hsym ?_ (fun ξ => (hbound ξ).2) i j
  intro ξ
  exact (mul_nonneg hlower (Finset.sum_nonneg fun k _ => sq_nonneg (ξ k))).trans (hbound ξ).1


end HeatKernel

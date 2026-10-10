-- Copyright (c) 2026 Scott Armstrong and Amélie Loher. All rights reserved.
-- Released under Apache 2.0 license as described in the file LICENSE.
module

public import HeatKernel.Kernel.CoordinateDerivatives
public import HeatKernel.Kernel.ClassicalHeatEquation
public import RothschildStein.S.Transposes
public import RothschildStein.Definitions.sumSquares

/-! # Classical heat equations under the time-space coordinate equivalence

Spatial slices preserve the horizontal sum of squares. Together with the time
chain rule, this identifies the coordinate equation with the usual heat equation.
-/

@[expose] public section

noncomputable section

open TopologicalSpace
open scoped BigOperators

namespace HeatKernel

open RothschildStein

/-- The sum of squares on a spatial slice equals the sum of squares of the lifted fields. -/
theorem sumSquares_spatial_coordinate_slice {n q : ℕ}
    (X : Fin q → (Fin n → ℝ) → Fin n → ℝ)
    (hX : ∀ i, ContDiff ℝ (⊤ : ℕ∞) (X i))
    (v : (Fin (1 + n) → ℝ) → ℝ)
    (hv : ContDiffOn ℝ (⊤ : ℕ∞) v {z | 0 < z 0})
    {t : ℝ} (ht : 0 < t) (x : Fin n → ℝ) :
    sumSquares X (fun y => v ((timeSpaceCoordinates n).symm (t, y))) x =
      ∑ i : Fin q, fieldDerivative (liftRightField 1 (X i))
        (fieldDerivative (liftRightField 1 (X i)) v) ((timeSpaceCoordinates n).symm (t, x)) := by
  let Ω : Opens (Fin (1 + n) → ℝ) := ⟨{z | 0 < z 0}, isOpen_positive_time n⟩
  have hmem (y : Fin n → ℝ) : (timeSpaceCoordinates n).symm (t, y) ∈ Ω := by
    change 0 < (timeSpaceCoordinates n).symm (t, y) 0
    simpa only [timeSpaceCoordinates_symm_time] using ht
  have hdiff (y : Fin n → ℝ) : DifferentiableAt ℝ v ((timeSpaceCoordinates n).symm (t, y)) :=
    (hv.contDiffAt (Ω.isOpen.mem_nhds (hmem y))).differentiableAt (by simp)
  unfold sumSquares
  apply Finset.sum_congr rfl
  intro i _
  have heq : fieldDerivative (X i) (fun y => v ((timeSpaceCoordinates n).symm (t, y))) =
      fun y => fieldDerivative (liftRightField 1 (X i)) v
        ((timeSpaceCoordinates n).symm (t, y)) :=
    funext fun y => fieldDerivative_spatial_coordinate_slice (X i) v t y (hdiff y)
  rw [heq]
  have hfirst := S.contDiffOn_fieldDerivative Ω (liftRightField 1 (X i)) v
    ((hX i).liftRightField 1).contDiffOn hv
  exact fieldDerivative_spatial_coordinate_slice (X i) _ t x
    ((hfirst.contDiffAt (Ω.isOpen.mem_nhds (hmem x))).differentiableAt (by simp))

/-- A smooth coordinate solution gives the classical time derivative and spatial sum of squares. -/
theorem deriv_eq_sumSquares_of_coordinate_heat_equation {n q : ℕ}
    (X : Fin q → (Fin n → ℝ) → Fin n → ℝ)
    (hX : ∀ i, ContDiff ℝ (⊤ : ℕ∞) (X i))
    (v : (Fin (1 + n) → ℝ) → ℝ)
    (hv : ContDiffOn ℝ (⊤ : ℕ∞) v {z | 0 < z 0})
    (hheat : ∀ z, 0 < z 0 →
      fderiv ℝ v z (leftCoordinateInclusion 1 n (fun _ => 1)) =
        ∑ i : Fin q, fieldDerivative (liftRightField 1 (X i))
          (fieldDerivative (liftRightField 1 (X i)) v) z)
    {t : ℝ} (ht : 0 < t) (x : Fin n → ℝ) :
    deriv (fun s => v ((timeSpaceCoordinates n).symm (s, x))) t =
      sumSquares X (fun y => v ((timeSpaceCoordinates n).symm (t, y))) x := by
  have hz : 0 < (timeSpaceCoordinates n).symm (t, x) 0 := by
    simpa only [timeSpaceCoordinates_symm_time] using ht
  rw [deriv_time_coordinate_slice v t x
    ((hv.contDiffAt ((isOpen_positive_time n).mem_nhds hz)).differentiableAt (by simp)),
    hheat _ hz, sumSquares_spatial_coordinate_slice X hX v hv ht x]

end HeatKernel

-- Copyright (c) 2026 Scott Armstrong and Amélie Loher. All rights reserved.
-- Released under Apache 2.0 license as described in the file LICENSE.
module

public import HeatKernel.Kernel.CoordinateHeatEquation
public import HeatKernel.Kernel.ClassicalWeakHeatEquation

/-! # Weak coordinate tests from classical slice equations

The coordinate chain rules work in both directions. Smooth classical equations
on every positive-time spatial slice therefore give the compact coordinate test identity.
-/

@[expose] public section

noncomputable section

open MeasureTheory
open scoped BigOperators

namespace HeatKernel

open RothschildStein

/-- The classical heat equation on slices implies its coordinate form. -/
theorem coordinate_heat_equation_of_slice_equation {n q : ℕ}
    (X : Fin q → (Fin n → ℝ) → Fin n → ℝ)
    (hX : ∀ i, ContDiff ℝ (⊤ : ℕ∞) (X i))
    (v : (Fin (1 + n) → ℝ) → ℝ)
    (hv : ContDiffOn ℝ (⊤ : ℕ∞) v {z | 0 < z 0})
    (hheat : ∀ t, 0 < t → ∀ x,
      deriv (fun s => v ((timeSpaceCoordinates n).symm (s, x))) t =
        sumSquares X (fun y => v ((timeSpaceCoordinates n).symm (t, y))) x)
    {z : Fin (1 + n) → ℝ} (hz : 0 < z 0) :
    fderiv ℝ v z (leftCoordinateInclusion 1 n (fun _ => 1)) =
      ∑ i : Fin q, fieldDerivative (liftRightField 1 (X i))
        (fieldDerivative (liftRightField 1 (X i)) v) z := by
  have ht : 0 < (timeSpaceCoordinates n z).1 := hz
  have hdiff : DifferentiableAt ℝ v
      ((timeSpaceCoordinates n).symm ((timeSpaceCoordinates n z).1, (timeSpaceCoordinates n z).2)) := by
    simpa only [Prod.mk.eta, ContinuousLinearEquiv.symm_apply_apply] using
      (hv.contDiffAt ((isOpen_positive_time n).mem_nhds hz)).differentiableAt (by simp)
  have h := hheat (timeSpaceCoordinates n z).1 ht (timeSpaceCoordinates n z).2
  rw [deriv_time_coordinate_slice v _ _ hdiff, sumSquares_spatial_coordinate_slice X hX v hv ht] at h
  simpa only [Prod.mk.eta, ContinuousLinearEquiv.symm_apply_apply] using h

/-- Smooth classical heat equations on slices give the literal weak coordinate test identity. -/
theorem integral_weak_heat_test_eq_zero_of_slice_equation {n q : ℕ}
    (G : HomogeneousGroup n) (hq : q ≤ n) (v : (Fin (1 + n) → ℝ) → ℝ)
    (hv : ContDiffOn ℝ (⊤ : ℕ∞) v {z | 0 < z 0})
    (hheat : ∀ t, 0 < t → ∀ x,
      deriv (fun s => v ((timeSpaceCoordinates n).symm (s, x))) t =
        sumSquares (G.horizontalFields hq)
          (fun y => v ((timeSpaceCoordinates n).symm (t, y))) x)
    (φ : (Fin (1 + n) → ℝ) → ℝ) (hφ : ContDiff ℝ (⊤ : ℕ∞) φ)
    (hc : HasCompactSupport φ) (hs : tsupport φ ⊆ {z | 0 < z 0}) :
    (∫ z in {z | 0 < z 0}, v z *
      (fderiv ℝ φ z (leftCoordinateInclusion 1 n (fun _ => 1)) +
        ∑ i : Fin q, fieldDerivative (liftRightField 1 (G.horizontalFields hq i))
          (fieldDerivative (liftRightField 1 (G.horizontalFields hq i)) φ) z)) = 0 := by
  apply integral_weak_heat_test_eq_zero_of_classical_equation G hq v hv
    (fun z hz => coordinate_heat_equation_of_slice_equation (G.horizontalFields hq)
      (G.horizontalFields_contDiff hq) v hv hheat hz) φ hφ hc hs

end HeatKernel

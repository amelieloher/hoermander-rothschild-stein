-- Copyright (c) 2026 Scott Armstrong and Amélie Loher. All rights reserved.
-- Released under Apache 2.0 license as described in the file LICENSE.
module

public import HeatKernel.Kernel.Coordinates
public import RothschildStein.Definitions.fieldDerivative
public import Mathlib.Analysis.Calculus.Deriv.Comp
public import Mathlib.Analysis.Calculus.FDeriv.Prod

/-! # Derivatives of time and space coordinate slices

The continuous linear coordinate equivalence identifies slice derivatives with
the corresponding coordinate inclusions and lifted vector fields.
-/

@[expose] public section

noncomputable section

namespace HeatKernel

open RothschildStein

/-- A spatial vector is included by the inverse time-space map with zero time. -/
theorem timeSpaceCoordinates_symm_zero_left {n : ℕ} (v : Fin n → ℝ) :
    (timeSpaceCoordinates n).symm (0, v) = rightCoordinateInclusion 1 n v := rfl

/-- The unit time vector is the first coordinate inclusion. -/
theorem timeSpaceCoordinates_symm_one_zero {n : ℕ} :
    (timeSpaceCoordinates n).symm (1, (0 : Fin n → ℝ)) =
      leftCoordinateInclusion 1 n (fun _ => 1) := rfl

/-- The spatial coordinate projection of a time-space slice is its spatial argument. -/
theorem rightCoordinateProjection_timeSpaceCoordinates_symm {n : ℕ}
    (t : ℝ) (x : Fin n → ℝ) :
    rightCoordinateProjection 1 n ((timeSpaceCoordinates n).symm (t, x)) = x := by
  change (timeSpaceCoordinates n ((timeSpaceCoordinates n).symm (t, x))).2 = x
  simp only [ContinuousLinearEquiv.apply_symm_apply]

/-- The inverse coordinate map preserves the time coordinate. -/
theorem timeSpaceCoordinates_symm_time {n : ℕ} (t : ℝ) (x : Fin n → ℝ) :
    (timeSpaceCoordinates n).symm (t, x) 0 = t := by
  change (timeSpaceCoordinates n ((timeSpaceCoordinates n).symm (t, x))).1 = t
  simp only [ContinuousLinearEquiv.apply_symm_apply]

/-- Differentiating a spatial slice applies the coordinate derivative to the spatial inclusion. -/
theorem fderiv_spatial_coordinate_slice {n : ℕ} (v : (Fin (1 + n) → ℝ) → ℝ)
    (t : ℝ) (x w : Fin n → ℝ)
    (hv : DifferentiableAt ℝ v ((timeSpaceCoordinates n).symm (t, x))) :
    fderiv ℝ (fun y => v ((timeSpaceCoordinates n).symm (t, y))) x w =
      fderiv ℝ v ((timeSpaceCoordinates n).symm (t, x)) (rightCoordinateInclusion 1 n w) := by
  have h := hv.hasFDerivAt.comp x
    ((timeSpaceCoordinates n).symm.hasFDerivAt.comp x (hasFDerivAt_prodMk_right t x))
  have heq := congrArg (fun L => L w) h.fderiv
  simpa only [Function.comp_def, ContinuousLinearMap.comp_apply,
    ContinuousLinearMap.inr_apply, ContinuousLinearEquiv.coe_coe,
    timeSpaceCoordinates_symm_zero_left] using heq

/-- Differentiating a time slice applies the coordinate derivative to the unit time vector. -/
theorem deriv_time_coordinate_slice {n : ℕ} (v : (Fin (1 + n) → ℝ) → ℝ)
    (t : ℝ) (x : Fin n → ℝ)
    (hv : DifferentiableAt ℝ v ((timeSpaceCoordinates n).symm (t, x))) :
    deriv (fun s => v ((timeSpaceCoordinates n).symm (s, x))) t =
      fderiv ℝ v ((timeSpaceCoordinates n).symm (t, x))
        (leftCoordinateInclusion 1 n (fun _ => 1)) := by
  have h := hv.hasFDerivAt.comp t
    ((timeSpaceCoordinates n).symm.hasFDerivAt.comp t (hasFDerivAt_prodMk_left t x))
  simpa only [Function.comp_def, ContinuousLinearMap.comp_apply,
    ContinuousLinearMap.inl_apply, ContinuousLinearEquiv.coe_coe,
    timeSpaceCoordinates_symm_one_zero] using h.hasDerivAt.deriv

/-- A spatial field derivative on a slice is the corresponding lifted field derivative. -/
theorem fieldDerivative_spatial_coordinate_slice {n : ℕ}
    (X : (Fin n → ℝ) → Fin n → ℝ) (v : (Fin (1 + n) → ℝ) → ℝ)
    (t : ℝ) (x : Fin n → ℝ)
    (hv : DifferentiableAt ℝ v ((timeSpaceCoordinates n).symm (t, x))) :
    fieldDerivative X (fun y => v ((timeSpaceCoordinates n).symm (t, y))) x =
      fieldDerivative (liftRightField 1 X) v ((timeSpaceCoordinates n).symm (t, x)) := by
  change fderiv ℝ _ x (X x) = fderiv ℝ v _ (rightCoordinateInclusion 1 n (X _))
  rw [rightCoordinateProjection_timeSpaceCoordinates_symm]
  exact fderiv_spatial_coordinate_slice v t x (X x) hv

end HeatKernel

-- Copyright (c) 2026 Scott Armstrong and Amélie Loher. All rights reserved.
-- Released under Apache 2.0 license as described in the file LICENSE.
module

public import RothschildStein.L1.HorizontalChartDerivative
public import Mathlib.Analysis.Normed.Module.FiniteDimension
public import Mathlib.Topology.Algebra.Module.Determinant

@[expose] public section
set_option autoImplicit false
set_option relaxedAutoImplicit false
noncomputable section
namespace RothschildStein.L1

/-- A nonzero actual finite-dimensional determinant constructs
the continuous linear equivalence needed by the parameterized inverse
theorem (BB pp. 520–521). -/
theorem exists_continuousLinearEquiv_of_det_ne_zero {E : Type*}
    [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]
    (L : E →L[ℝ] E) (hdet : L.det ≠ 0) :
    ∃ H : E ≃L[ℝ] E, L = (H : E →L[ℝ] E) := by
  have hu : IsUnit L.toLinearMap :=
    (LinearMap.isUnit_iff_isUnit_det _).mpr (isUnit_iff_ne_zero.mpr hdet)
  let H := (LinearEquiv.ofBijective L.toLinearMap ((Module.End.isUnit_iff _).mp hu)).toContinuousLinearEquiv
  refine ⟨H,?_⟩
  ext x
  rfl

end RothschildStein.L1

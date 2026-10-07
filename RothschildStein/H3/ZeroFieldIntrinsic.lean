-- Copyright (c) 2026 Scott Armstrong and Amélie Loher. All rights reserved.
-- Released under Apache 2.0 license as described in the file LICENSE.
module

public import RothschildStein.S.WeakToIntrinsic

set_option autoImplicit false
set_option relaxedAutoImplicit false
@[expose] public section
noncomputable section
open Set MeasureTheory TopologicalSpace
namespace RothschildStein.H3

/-- The zero field has zero formal transpose on every test input. -/
theorem fieldTranspose_zero_field {N : ℕ}
    (φ : (Fin N → ℝ) → ℝ) (x : Fin N → ℝ) :
    fieldTranspose (0 : (Fin N → ℝ) → (Fin N → ℝ)) φ x = 0 := by
  simp [fieldTranspose, Hormander.Interface.euclideanDivergence]

/-- Every continuous scalar function has zero intrinsic derivative
along the zero field. The weak-to-intrinsic theorem supplies both
existence of integral curves and the derivative along all such curves. -/
theorem hasIntrinsicDeriv_zero_field {N : ℕ}
    (U : Opens (Fin N → ℝ)) (u : (Fin N → ℝ) → ℝ)
    (hu : ContinuousOn u (U : Set (Fin N → ℝ))) :
    hasIntrinsicDeriv U (0 : (Fin N → ℝ) → (Fin N → ℝ)) u 0 := by
  apply S.hasIntrinsicDeriv_of_continuous_weak_derivative U 0
    contDiffOn_const u 0 hu continuousOn_const
  refine ⟨hu.locallyIntegrableOn U.isOpen.measurableSet,
    continuousOn_const.locallyIntegrableOn U.isOpen.measurableSet, ?_⟩
  intro φ
  simp [wordTranspose, fieldTranspose_zero_field]

end RothschildStein.H3

-- Copyright (c) 2026 Scott Armstrong and Amélie Loher. All rights reserved.
-- Released under Apache 2.0 license as described in the file LICENSE.
module

public import HeatKernel.Moser.CaccioppoliMatrixPowerFlux
public import HeatKernel.Moser.MeanValueHalfPowerEnergy
public import HeatKernel.Moser.CaccioppoliSpatialPowerTest
public import HeatKernel.Moser.WeakSolutionSpatialTransport
import Mathlib.Tactic

/-! # Spatial absorption of the elliptic matrix power flux -/

@[expose] public section
set_option autoImplicit false
set_option relaxedAutoImplicit false
noncomputable section
open Set MeasureTheory TopologicalSpace
namespace HeatKernel

/-- The cutoff loss in either truncation region is bounded by twice the
square of the same half-power transform. -/
theorem caccioppoli_power_cutoff_error_le_half_sq {M p s : ℝ}
    (hM : 0 < M) (hp : 2 ≤ p) (hs : 0 ≤ s) :
    (if s < M then (2 / (p - 1)) * s ^ p else 2 * (s ^ 2 * M ^ (p - 2))) ≤
      2 * linearTailPositivePower M (p / 2) s ^ 2 := by
  by_cases hl : s < M
  · rw [ite_eq_left hl, linearTailPositivePower_eq_rpow hs hl.le,
      ← Real.rpow_two, ← Real.rpow_mul hs]
    have he : p / 2 * 2 = p := by ring
    rw [he]
    apply mul_le_mul_of_nonneg_right _ (Real.rpow_nonneg hs p)
    apply (div_le_iff₀ (show 0 < p - 1 by linarith)).mpr
    linarith
  · rw [ite_eq_right hl, linearTailPositivePower_eq_linear hM (le_of_not_gt hl),
      mul_pow, ← Real.rpow_two (M ^ (p / 2 - 1)), ← Real.rpow_mul hM.le]
    have he : (p / 2 - 1) * 2 = p - 2 := by ring
    rw [he]
    ring_nf
    exact le_rfl

end HeatKernel

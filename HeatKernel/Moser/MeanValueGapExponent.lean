-- Copyright (c) 2026 Scott Armstrong and Amélie Loher. All rights reserved.
-- Released under Apache 2.0 license as described in the file LICENSE.
module

public import HeatKernel.Moser.MeanValueNestedIteration
import Mathlib.Tactic

/-! # The cutoff-gap exponent in parabolic mean-value bounds -/

@[expose] public section
set_option autoImplicit false
set_option relaxedAutoImplicit false
namespace HeatKernel

/-- The convergent cutoff product separates into a geometric constant and a gap power. -/
theorem cutoff_iteration_constant_eq_gap_power {C B δ χ : ℝ}
    (hC : 0 < C) (hB : 0 < B) (hδ : 0 < δ) :
    Real.exp (((Real.log C - 2 * Real.log δ) / 2) * (1 - χ⁻¹)⁻¹ +
      (Real.log B / 2) * (χ⁻¹ / (1 - χ⁻¹) ^ 2)) =
      C ^ ((1 - χ⁻¹)⁻¹ / 2) *
        B ^ ((χ⁻¹ / (1 - χ⁻¹) ^ 2) / 2) * δ ^ (-(1 - χ⁻¹)⁻¹) := by
  rw [Real.rpow_def_of_pos hC, Real.rpow_def_of_pos hB, Real.rpow_def_of_pos hδ,
    ← Real.exp_add, ← Real.exp_add]
  congr 1
  ring

/-- The parabolic cutoff-gap exponent is one plus half the Sobolev dimension. -/
theorem parabolic_cutoff_gap_exponent {ν : ℝ} (hν : 2 < ν) :
    (1 - (1 + 2 / ν)⁻¹)⁻¹ = 1 + ν / 2 := by
  have hn : ν ≠ 0 := by linarith
  have hd : ν + 2 ≠ 0 := by linarith
  field_simp
  ring

end HeatKernel

-- Copyright (c) 2026 Scott Armstrong and Amélie Loher. All rights reserved.
-- Released under Apache 2.0 license as described in the file LICENSE.
module

public import Mathlib

/-! Exponent-uniform coefficients for reciprocal-power energy estimates. -/

set_option autoImplicit false
set_option relaxedAutoImplicit false
@[expose] public section
namespace HeatKernel

/-- For the parabolic exponent ratio, the geometric accumulation has the precise
coefficient used in the spatial and temporal gap power. -/
theorem negative_power_parabolic_geometric_coefficients {ν : ℝ} (hν : 0 < ν) :
    (1 - ν / (ν + 2))⁻¹ = (ν + 2) / 2 ∧
      (ν / (ν + 2)) / (1 - ν / (ν + 2)) ^ 2 = ν * (ν + 2) / 4 := by
  have hn : ν + 2 ≠ 0 := by positivity
  have hd : 1 - ν / (ν + 2) = 2 / (ν + 2) := by field_simp; ring
  rw [hd]
  constructor
  · field_simp [hn]
  · field_simp [hn]
    ring

end HeatKernel

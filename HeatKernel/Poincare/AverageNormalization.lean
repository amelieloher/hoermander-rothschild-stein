-- Copyright (c) 2026 Scott Armstrong and Amélie Loher. All rights reserved.
-- Released under Apache 2.0 license as described in the file LICENSE.
module

public import Mathlib.MeasureTheory.Integral.Average
public import Mathlib.Analysis.SpecialFunctions.Pow.Real
public import Mathlib.Tactic.FieldSimp
public import Mathlib.Tactic.Ring
public import Mathlib.Tactic.Positivity

/-! Normalization of integral inequalities and their positive-power roots. -/

@[expose] public section
set_option autoImplicit false
set_option relaxedAutoImplicit false
noncomputable section
open Set MeasureTheory

namespace HeatKernel

/-- Integral comparison becomes average comparison after inserting the ratio of the
containing and original measures. -/
theorem average_le_of_integral_le {E V : Type*} [MeasurableSpace E] [MeasurableSpace V]
    (μ : Measure E) (ν : Measure V) {f : E → ℝ} {g : V → ℝ} {A C : ℝ}
    (hμ : 0 < μ.real univ) (hC : 0 < C)
    (hvolume : ν.real univ = C * μ.real univ)
    (h : (∫ x, f x ∂μ) ≤ A * ∫ y, g y ∂ν) :
    (⨍ x, f x ∂μ) ≤ A * C * ⨍ y, g y ∂ν := by
  rw [average_eq, average_eq, smul_eq_mul, smul_eq_mul]
  calc
    (μ.real univ)⁻¹ * (∫ x, f x ∂μ) ≤ (μ.real univ)⁻¹ * (A * ∫ y, g y ∂ν) :=
      mul_le_mul_of_nonneg_left h (inv_nonneg.mpr hμ.le)
    _ = A * C * ((ν.real univ)⁻¹ * ∫ y, g y ∂ν) := by
      rw [hvolume]
      field_simp [hμ.ne', hC.ne']

end HeatKernel

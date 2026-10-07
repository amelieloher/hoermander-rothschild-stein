-- Copyright (c) 2026 Scott Armstrong and Amélie Loher. All rights reserved.
-- Released under Apache 2.0 license as described in the file LICENSE.
module

public import RothschildStein.S.FriedrichsKernelDefs
public import RothschildStein.S.CoordinateDilationIntegral
public import Mathlib.MeasureTheory.Group.Integral

set_option autoImplicit false
set_option relaxedAutoImplicit false
@[expose] public section
noncomputable section
open Set MeasureTheory Function
namespace RothschildStein.S
variable {n : ℕ}

/-- The fixed-displacement kernel operator equals its
rescaled integration-variable form, with no integrability or dimension
restriction added to the change of variables (BB (2.11), p. 78). -/
theorem friedrichsKernelOp_eq_rescaled
    (K : ℝ → (Fin n → ℝ) → (Fin n → ℝ) → ℝ) (h : (Fin n → ℝ) → ℝ)
    {ε : ℝ} (hε : 0 < ε) (x : Fin n → ℝ) :
    friedrichsKernelOp K h ε x = ∫ z, h z * friedrichsRescaledKernel K ε x z := by
  have H := integral_coordinate_smul hε (fun z => K ε x (ε⁻¹ • z) * h (x+z))
  simp only [smul_smul,inv_mul_cancel₀ hε.ne',one_smul] at H
  have ht := integral_add_left_eq_self (μ := volume)
    (fun z : Fin n → ℝ => K ε x (ε⁻¹ • (z-x)) * h z) x
  have he (z : Fin n → ℝ) : x+z-x = z := by abel
  simp only [he] at ht
  unfold friedrichsKernelOp friedrichsRescaledKernel
  have hm : (fun z : Fin n → ℝ => h z * ((ε^n)⁻¹ * K ε x (ε⁻¹ • (z-x)))) =
      fun z => (ε^n)⁻¹ * (K ε x (ε⁻¹ • (z-x)) * h z) := by
    funext z
    ring
  rw [hm,integral_const_mul,← ht]
  exact H

end RothschildStein.S

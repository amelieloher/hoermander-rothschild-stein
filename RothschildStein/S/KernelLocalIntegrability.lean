-- Copyright (c) 2026 Scott Armstrong and Amélie Loher. All rights reserved.
-- Released under Apache 2.0 license as described in the file LICENSE.
module

public import RothschildStein.S.RescaledKernelTest
public import RothschildStein.S.WeakDeriv
public import Mathlib.MeasureTheory.Group.Integral
public import Mathlib.MeasureTheory.Measure.Haar.NormedSpace

set_option autoImplicit false
set_option relaxedAutoImplicit false
set_option backward.isDefEq.respectTransparency false
@[expose] public section
noncomputable section
open Set MeasureTheory Function Metric TopologicalSpace
open scoped Topology ContDiff
namespace RothschildStein.S
variable {n : ℕ}

/-- A kernel section paired with locally integrable data is integrable in the displacement variable; translation and scaling account for the Jacobian factor (BB pp. 74–78). -/
theorem integrable_smoothFriedrichsKernel_section
    (Ω : Opens (Fin n → ℝ)) (K : SmoothFriedrichsKernel n)
    {h : (Fin n → ℝ) → ℝ} (hh : LocallyIntegrableOn h (Ω : Set (Fin n → ℝ)) volume)
    {ε : ℝ} (hε : 0 < ε) (x : Fin n → ℝ) (hx : closedBall x ε ⊆ Ω) :
    Integrable (fun y => K.family ε x y * h (x+ε • y)) volume := by
  let φ := rescaledKernelTest Ω K hε x hx
  have hi := integrable_mul_test Ω hh φ
  have H := ((hi.comp_add_left x).comp_smul hε.ne').const_mul (ε^n)
  have he : (fun y : Fin n → ℝ => ε^n * (h (x+ε • y) * φ (x+ε • y))) =
      fun y => K.family ε x y * h (x+ε • y) := by
    funext y
    change ε^n * (h (x+ε • y) * ((ε^n)⁻¹ * K.family ε x (ε⁻¹ • (x+ε • y-x)))) = _
    rw [add_sub_cancel_left,smul_smul,inv_mul_cancel₀ hε.ne',one_smul]
    have hp : (ε^n) * (ε^n)⁻¹ = 1 := mul_inv_cancel₀ (pow_ne_zero _ hε.ne')
    calc
      _ = (ε^n * (ε^n)⁻¹) * (K.family ε x y * h (x+ε • y)) := by ring
      _ = _ := by rw [hp,one_mul]
  change Integrable (fun y : Fin n → ℝ => ε^n * (h (x+ε • y) * φ (x+ε • y))) volume at H
  rw [he] at H
  exact H

/-- Vanishing mean gives the increment identity for locally
integrable data, including Lp representatives which need not be
continuous (BB Lemma 2.11, p. 74). -/
theorem smoothFriedrichsKernel_op_eq_increment
    (Ω : Opens (Fin n → ℝ)) (K : SmoothFriedrichsKernel n)
    {h : (Fin n → ℝ) → ℝ} (hh : LocallyIntegrableOn h (Ω : Set (Fin n → ℝ)) volume)
    {ε : ℝ} (hε : 0 < ε) (x : Fin n → ℝ) (hx : closedBall x ε ⊆ Ω)
    (hmean : (∫ y, K.family ε x y) = 0) :
    friedrichsKernelOp K.family h ε x = ∫ y, K.family ε x y * (h (x+ε • y)-h x) := by
  unfold friedrichsKernelOp
  simp only [mul_sub]
  rw [integral_sub (integrable_smoothFriedrichsKernel_section Ω K hh hε x hx)
    (((K.section_smooth ε x).continuous.integrable_of_hasCompactSupport
      (K.section_compact ε x)).mul_const (h x)),
    integral_mul_const,hmean,MulZeroClass.zero_mul,sub_zero]

end RothschildStein.S

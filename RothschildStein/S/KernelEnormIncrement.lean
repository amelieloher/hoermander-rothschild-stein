-- Copyright (c) 2026 Scott Armstrong and Amélie Loher. All rights reserved.
-- Released under Apache 2.0 license as described in the file LICENSE.
module

public import RothschildStein.S.KernelLocalIntegrability
public import Mathlib.MeasureTheory.Integral.Bochner.Basic

set_option autoImplicit false
set_option relaxedAutoImplicit false
set_option backward.isDefEq.respectTransparency false
@[expose] public section
noncomputable section
open Set MeasureTheory Function Metric TopologicalSpace
open scoped ENNReal
namespace RothschildStein.S
variable {n : ℕ}

/-- The pointwise kernel bound in extended norms for merely
locally integrable data; integration is confined to the unit displacement
ball (BB Lemma 2.11, p. 74). -/
theorem enorm_smoothFriedrichsKernelOp_le_increment
    (Ω : Opens (Fin n → ℝ)) (K : SmoothFriedrichsKernel n)
    {h : (Fin n → ℝ) → ℝ} (hh : LocallyIntegrableOn h (Ω : Set (Fin n → ℝ)) volume)
    {ε : ℝ} (hε : 0 < ε) (x : Fin n → ℝ) (hx : closedBall x ε ⊆ Ω)
    (hmean : (∫ y, K.family ε x y) = 0) (C : ℝ)
    (hsize : ∀ y, ‖K.family ε x y‖ ≤ C) :
    ‖friedrichsKernelOp K.family h ε x‖ₑ ≤
      ENNReal.ofReal C * ∫⁻ y in closedBall (0 : Fin n → ℝ) 1,
        ‖h (x+ε • y)-h x‖ₑ := by
  rw [smoothFriedrichsKernel_op_eq_increment Ω K hh hε x hx hmean]
  apply (enorm_integral_le_lintegral_enorm _).trans
  have hb : ∫⁻ y, ‖K.family ε x y * (h (x+ε • y)-h x)‖ₑ ≤
      ∫⁻ y, (closedBall (0 : Fin n → ℝ) 1).indicator
        (fun y => ENNReal.ofReal C * ‖h (x+ε • y)-h x‖ₑ) y := by
    apply lintegral_mono
    intro y
    change ‖K.family ε x y * (h (x+ε • y)-h x)‖ₑ ≤
      (closedBall (0 : Fin n → ℝ) 1).indicator
        (fun y => ENNReal.ofReal C * ‖h (x+ε • y)-h x‖ₑ) y
    by_cases hy : y ∈ closedBall (0 : Fin n → ℝ) 1
    · rw [indicator_of_mem hy,enorm_mul]
      apply mul_le_mul_left
      rw [← ofReal_norm]
      exact ENNReal.ofReal_le_ofReal (hsize y)
    · have hz : K.family ε x y = 0 :=
        K.vanish ((x,y),ε) (lt_of_not_ge (by simpa only [mem_closedBall,dist_zero_right] using hy))
      rw [hz,zero_mul,enorm_zero,indicator_of_notMem hy]
  refine hb.trans_eq ?_
  rw [lintegral_indicator isClosed_closedBall.measurableSet,
    lintegral_const_mul' _ _ ENNReal.ofReal_ne_top]

end RothschildStein.S

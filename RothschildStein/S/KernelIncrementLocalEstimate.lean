-- Copyright (c) 2026 Scott Armstrong and Amélie Loher. All rights reserved.
-- Released under Apache 2.0 license as described in the file LICENSE.
module

public import RothschildStein.S.KernelCancellationLocal
public import Mathlib.MeasureTheory.Integral.Bochner.Set

set_option autoImplicit false
set_option relaxedAutoImplicit false
set_option backward.isDefEq.respectTransparency false
@[expose] public section
noncomputable section
open Set MeasureTheory Function Metric
namespace RothschildStein.S
variable {n : ℕ} {U : Set (Fin n → ℝ)} {δ : ℝ}

/-- For local continuous data, a zero-mean kernel is bounded by its
size, unit-ball volume, and an increment bound on the translated support (BB Lemma 2.21, p. 87). -/
theorem norm_friedrichsKernelOp_le_increment_of_continuousOn (K : BoundedFriedrichsKernel U δ)
    (hK : HasVanishingKernelMean K) {h : (Fin n → ℝ) → ℝ}
    {L : Set (Fin n → ℝ)} (hh : ContinuousOn h L) {ε : ℝ} (hε : ε ∈ Ioo 0 δ)
    {x : Fin n → ℝ} (hx : x ∈ U)
    (hL : ∀ y ∈ closedBall (0 : Fin n → ℝ) 1, x+ε • y ∈ L) (C D : ℝ) (hC : 0 ≤ C)
    (hsize : ∀ y, ‖K.toFun ε x y‖ ≤ C)
    (hinc : ∀ y ∈ closedBall (0 : Fin n → ℝ) 1,
      ‖h (x+ε • y)-h x‖ ≤ D) :
    ‖friedrichsKernelOp K.toFun h ε x‖ ≤
      C * (volume (closedBall (0 : Fin n → ℝ) 1)).toReal * D := by
  let B := closedBall (0 : Fin n → ℝ) 1
  have hi : Integrable (B.indicator (fun _ => C*D)) volume := by
    rw [integrable_indicator_iff isClosed_closedBall.measurableSet]
    exact integrableOn_const (measure_closedBall_lt_top.ne)
  have hb : ∀ᵐ y ∂volume,
      ‖K.toFun ε x y * (h (x+ε • y)-h x)‖ ≤ B.indicator (fun _ => C*D) y := by
    apply Filter.Eventually.of_forall
    intro y
    by_cases hy : y ∈ B
    · rw [indicator_of_mem hy,norm_mul]
      exact mul_le_mul (hsize y) (hinc y hy) (norm_nonneg _) hC
    · have hz : K.toFun ε x y = 0 := by
        by_contra hn
        exact hy (K.support ε hε x hx hn)
      rw [hz,MulZeroClass.zero_mul,norm_zero,indicator_of_notMem hy]
  rw [friedrichsKernelOp_eq_increment_of_continuousOn K hK hh hε hx hL]
  have H := norm_integral_le_of_norm_le hi hb
  rw [integral_indicator isClosed_closedBall.measurableSet,setIntegral_const] at H
  simpa only [smul_eq_mul] using H.trans_eq (by simp only [Measure.real_def]; ring)

end RothschildStein.S

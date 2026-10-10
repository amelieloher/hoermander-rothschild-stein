-- Copyright (c) 2026 Scott Armstrong and Amélie Loher. All rights reserved.
-- Released under Apache 2.0 license as described in the file LICENSE.
module

public import HeatKernel.Moser.WeakSolutionScalarTests
public import HeatKernel.Moser.WeakSolutionCutoffDualEquation
import Mathlib.Tactic

/-! # Normalization of the reciprocal energy test -/

@[expose] public section
set_option autoImplicit false
set_option relaxedAutoImplicit false
noncomputable section
open Set MeasureTheory
open scoped NNReal

namespace HeatKernel

/-- The centered negative first power is the reciprocal test on nonnegative inputs. -/
theorem shiftedReciprocalWeakSolutionTest_eq {c s : ℝ} (hc : 0 < c) (hs : 0 ≤ s) :
    (shiftedRpowWeakSolutionTest hc (p := -1) (by norm_num)).toFun s =
      (s + c)⁻¹ - c⁻¹ := by
  simpa only [shiftedRpowWeakSolutionTest, Real.rpow_neg_one] using
    Sobolev.zeroPreservingShiftedRpow_eq (c := c) (p := -1) hs

/-- The reciprocal test's primitive includes the linear correction from centering. -/
theorem shiftedReciprocalWeakSolutionTest_primitive {c s : ℝ}
    (hc : 0 < c) (hs : 0 ≤ s) :
    (shiftedRpowWeakSolutionTest hc (p := -1) (by norm_num)).primitive s =
      Real.log (s + c) - Real.log c - s * c⁻¹ := by
  let T := shiftedRpowWeakSolutionTest hc (p := (-1 : ℝ)) (by norm_num)
  have hd : ∀ x ∈ uIcc (0 : ℝ) s,
      HasDerivAt (fun y : ℝ => Real.log (y + c) - y * c⁻¹) (T.toFun x) x := by
    intro x hx
    have hx0 : 0 ≤ x := (uIcc_of_le hs ▸ hx).1
    rw [show T.toFun x = (x + c)⁻¹ - c⁻¹ from
      shiftedReciprocalWeakSolutionTest_eq hc hx0]
    have hpos : 0 < x + c := add_pos_of_nonneg_of_pos hx0 hc
    simpa only [Function.comp_def, Pi.sub_def, id_eq, mul_one, one_mul] using
      ((Real.hasDerivAt_log hpos.ne').comp x ((hasDerivAt_id x).add_const c)).sub
        ((hasDerivAt_id x).mul_const c⁻¹)
  have h := intervalIntegral.integral_eq_sub_of_hasDerivAt hd
    (T.lipschitz.continuous.intervalIntegrable 0 s)
  change (∫ x in (0 : ℝ)..s, T.toFun x) = _
  rw [h]
  simp only [zero_add, zero_mul, sub_zero]
  ring

end HeatKernel

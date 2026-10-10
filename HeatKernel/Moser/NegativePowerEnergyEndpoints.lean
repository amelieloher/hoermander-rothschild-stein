-- Copyright (c) 2026 Scott Armstrong and Amélie Loher. All rights reserved.
-- Released under Apache 2.0 license as described in the file LICENSE.
module

public import HeatKernel.Moser.WeakSolutionScalarTests
public import HeatKernel.Moser.WeakSolutionSpatialEnergyIdentity
import Mathlib.Tactic

/-! Spatially weighted reciprocal-power endpoint energies with their centering correction. -/

set_option autoImplicit false
set_option relaxedAutoImplicit false
@[expose] public section
noncomputable section
open Set MeasureTheory TopologicalSpace
namespace HeatKernel

/-- The normalized negative-power primitive retains the linear centering term. -/
theorem negative_power_test_primitive {c p s : ℝ}
    (hc : 0 < c) (hp : 0 < p) (hs : 0 ≤ s) :
    (shiftedRpowWeakSolutionTest hc (p := -p - 1) (by linarith)).primitive s =
      -((s + c) ^ (-p) - c ^ (-p)) / p - s * c ^ (-p - 1) := by
  let T := shiftedRpowWeakSolutionTest hc (p := -p - 1) (by linarith)
  have hd : ∀ x ∈ uIcc (0 : ℝ) s,
      HasDerivAt (fun y : ℝ => -(y + c) ^ (-p) / p - y * c ^ (-p - 1))
        (T.toFun x) x := by
    intro x hx
    have hx0 : 0 ≤ x := (uIcc_of_le hs ▸ hx).1
    have hpos : 0 < x + c := add_pos_of_nonneg_of_pos hx0 hc
    have he : T.toFun x = (x + c) ^ (-p - 1) - c ^ (-p - 1) :=
      Sobolev.zeroPreservingShiftedRpow_eq (c := c) (p := -p - 1) hx0
    rw [he]
    convert (((Real.hasDerivAt_rpow_const (p := -p) (Or.inl hpos.ne')).comp x
      ((hasDerivAt_id x).add_const c)).neg.div_const p).sub
      ((hasDerivAt_id x).mul_const (c ^ (-p - 1))) using 1 <;>
      simp only [Function.comp_def, mul_one, one_mul] <;>
      first | (ext y <;> dsimp) | field_simp [hp.ne']
  have he := intervalIntegral.integral_eq_sub_of_hasDerivAt hd
    (T.lipschitz.continuous.intervalIntegrable 0 s)
  change (∫ x in (0 : ℝ)..s, T.toFun x) = _
  rw [he]
  simp only [zero_add, zero_mul, sub_zero]
  ring

end HeatKernel

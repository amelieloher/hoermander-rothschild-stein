-- Copyright (c) 2026 Scott Armstrong and Amélie Loher. All rights reserved.
-- Released under Apache 2.0 license as described in the file LICENSE.
module

public import Mathlib.MeasureTheory.Function.LpSeminorm.ChebyshevMarkov
public import Mathlib.MeasureTheory.Function.AEEqOfLIntegral
public import Mathlib.Analysis.SpecialFunctions.Log.ENNRealLogExp
import Mathlib.Tactic

/-! # Essential bounds from arbitrarily high integral exponents -/

@[expose] public section
set_option autoImplicit false
set_option relaxedAutoImplicit false
open MeasureTheory Filter
open scoped ENNReal Topology
namespace HeatKernel

/-- Uniform bounds at exponents tending to infinity control the essential supremum. -/
theorem eLpNormEssSup_le_of_unbounded_exponents
    {α : Type*} [MeasurableSpace α] (μ : Measure α) {f : α → ℝ}
    {p : ℕ → ℝ} {K : ℝ≥0∞} (hp : ∀ j, 0 < p j)
    (hptop : Tendsto p atTop atTop)
    (hbound : ∀ j, eLpNorm f (ENNReal.ofReal (p j)) μ ≤ K) :
    eLpNormEssSup f μ ≤ K := by
  rw [eLpNormEssSup_eq_essSup_enorm]
  refine essSup_le_of_ae_le K ?_ (by isBoundedDefault)
  change ∀ᵐ x ∂μ, ‖f x‖ₑ ≤ K
  rw [ae_le_const_iff_forall_gt_measure_zero]
  intro ε hKε
  have hε : ε ≠ 0 := (lt_of_le_of_lt bot_le hKε).ne'
  have hr : ε⁻¹ * K < 1 := by
    rw [mul_comm, ← div_eq_mul_inv]
    exact ENNReal.div_lt_of_lt_mul (by simpa only [one_mul] using hKε)
  have ht : Tendsto (fun j => (ε⁻¹ * K) ^ (p j)) atTop (𝓝 0) :=
    (ENNReal.tendsto_rpow_atTop_of_base_lt_one hr).comp hptop
  apply le_antisymm _ bot_le
  apply ge_of_tendsto' ht
  intro j
  have hm := meas_ge_le_mul_pow_eLpNorm_enorm μ
    (ENNReal.ofReal_pos.mpr (hp j)).ne' ENNReal.ofReal_ne_top
    (f := f) hε (fun _ => by simp)
  rw [ENNReal.toReal_ofReal (hp j).le] at hm
  apply hm.trans
  rw [ENNReal.mul_rpow_of_nonneg _ _ (hp j).le]
  exact mul_le_mul' le_rfl (ENNReal.rpow_le_rpow (hbound j) (hp j).le)

end HeatKernel

-- Copyright (c) 2026 Scott Armstrong and Amélie Loher. All rights reserved.
-- Released under Apache 2.0 license as described in the file LICENSE.
module

public import RothschildStein.H2.OperatorAboveTwo
public import RothschildStein.H2.OperatorL2Norm

@[expose] public section
set_option autoImplicit false
set_option relaxedAutoImplicit false
noncomputable section
open Set MeasureTheory
open scoped ENNReal

namespace RothschildStein.H2
variable {X : Type*} [MeasurableSpace X]

/-- The single-operator coefficient for the Lᵖ bound. -/
def operatorAllExponentConstant (C Cs cT p : ℝ) : ℝ :=
  if p < 2 then operatorInterpolationConstant C cT p else
    if p = 2 then cT else operatorInterpolationConstant Cs cT (Real.conjExponent p)

/-- The all-exponent norm bound on the L²/Lᵖ intersection,
using the exact weak endpoints and L² adjointness
(BB p. 326). -/
theorem operator_lp_all_of_weak_one_one (μ : Measure X) [IsFiniteMeasure μ]
    (T Ts : Lp ℝ 2 μ →L[ℝ] Lp ℝ 2 μ) {cT C Cs p : ℝ}
    (hcT : ‖T‖ ≤ cT) (hcTs : ‖Ts‖ ≤ cT) (hC : 0 ≤ C) (hCs : 0 ≤ Cs)
    (hadj : ∀ v w : Lp ℝ 2 μ, (∫ x, (T v) x * w x ∂μ) = ∫ x, v x * (Ts w) x ∂μ)
    (hweak : ∀ v : Lp ℝ 2 μ, ∀ t : ℝ, 0 < t →
      distribution μ (fun x => (T v) x) t ≤ ENNReal.ofReal (C / t) * eLpNorm v 1 μ)
    (hweaks : ∀ v : Lp ℝ 2 μ, ∀ t : ℝ, 0 < t →
      distribution μ (fun x => (Ts v) x) t ≤ ENNReal.ofReal (Cs / t) * eLpNorm v 1 μ)
    (hp : 1 < p) (v : Lp ℝ 2 μ) (hvp : MemLp v (ENNReal.ofReal p) μ) :
    MemLp (fun x => (T v) x) (ENNReal.ofReal p) μ ∧
      eLpNorm (fun x => (T v) x) (ENNReal.ofReal p) μ ≤
        ENNReal.ofReal (operatorAllExponentConstant C Cs cT p) * eLpNorm v (ENNReal.ofReal p) μ := by
  by_cases hlt : p < 2
  · have hbase : 0 ≤ p * (2 * C / (p - 1) + 4 * cT ^ 2 / (2 - p)) := by
      have hp0 : 0 < p := by linarith
      have hpm : 0 < p - 1 := by linarith
      have hmp : 0 < 2 - p := by linarith
      positivity
    have hb := operator_lp_below_two_of_weak_one_one μ T hcT hC hweak v hp hlt hvp
    rw [ENNReal.ofReal_rpow_of_nonneg hbase (div_nonneg (by norm_num) (by linarith : 0 ≤ p))] at hb
    simpa only [operatorAllExponentConstant, ite_eq_left hlt, operatorInterpolationConstant] using hb
  · by_cases heq : p = 2
    · subst p
      simpa only [operatorAllExponentConstant, lt_self_iff_false, ite_false, ite_true,
        ENNReal.ofReal_ofNat] using
        (show MemLp (fun x => (T v) x) 2 μ ∧ eLpNorm (fun x => (T v) x) 2 μ ≤
          ENNReal.ofReal cT * eLpNorm v 2 μ from ⟨Lp.memLp _, operator_l2_eLpNorm_le μ T hcT v⟩)
    · have hb := operator_lp_above_two_of_weak_one_one μ T Ts hcTs hCs hadj hweaks
        (lt_of_le_of_ne (le_of_not_gt hlt) (Ne.symm heq) : 2 < p) v hvp
      simpa only [operatorAllExponentConstant, ite_eq_right hlt, ite_eq_right heq] using hb

end RothschildStein.H2

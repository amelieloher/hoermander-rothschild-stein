-- Copyright (c) 2026 Scott Armstrong and Amélie Loher. All rights reserved.
-- Released under Apache 2.0 license as described in the file LICENSE.
module

public import RothschildStein.H2.OperatorDuality
public import RothschildStein.H2.OperatorBelowTwoExtension

@[expose] public section
set_option autoImplicit false
set_option relaxedAutoImplicit false
noncomputable section
open Set MeasureTheory
open scoped ENNReal

namespace RothschildStein.H2
variable {X : Type*} [MeasurableSpace X]

/-- The transpose's exact weak endpoint and L² adjointness
suffice for the p > 2 norm estimate (BB p. 326). -/
theorem operator_lp_above_two_of_weak_one_one (μ : Measure X) [IsFiniteMeasure μ]
    (T Ts : Lp ℝ 2 μ →L[ℝ] Lp ℝ 2 μ) {cT C p : ℝ}
    (hcT : ‖Ts‖ ≤ cT) (hC : 0 ≤ C)
    (hadj : ∀ v w : Lp ℝ 2 μ, (∫ x, (T v) x * w x ∂μ) = ∫ x, v x * (Ts w) x ∂μ)
    (hweak : ∀ w : Lp ℝ 2 μ, ∀ t : ℝ, 0 < t →
      distribution μ (fun x => (Ts w) x) t ≤ ENNReal.ofReal (C / t) * eLpNorm w 1 μ)
    (hp : 2 < p) (v : Lp ℝ 2 μ) (hvp : MemLp v (ENNReal.ofReal p) μ) :
    MemLp (fun x => (T v) x) (ENNReal.ofReal p) μ ∧
      eLpNorm (fun x => (T v) x) (ENNReal.ofReal p) μ ≤
        ENNReal.ofReal (operatorInterpolationConstant C cT (Real.conjExponent p)) *
          eLpNorm v (ENNReal.ofReal p) μ := by
  let q := Real.conjExponent p
  have hp1 : 1 < p := by linarith
  have hpq : p.HolderConjugate q := Real.HolderConjugate.conjExponent hp1
  have hq1 : 1 < q := hpq.symm.lt
  have hq2 : q < 2 := by
    change p / (p - 1) < 2
    apply (div_lt_iff₀ (by linarith : 0 < p - 1)).mpr
    linarith
  have hbase : 0 ≤ q * (2 * C / (q - 1) + 4 * cT ^ 2 / (2 - q)) := by
    have hq0 : 0 < q := by linarith
    have hqm : 0 < q - 1 := by linarith
    have hmq : 0 < 2 - q := by linarith
    positivity
  apply operator_lp_of_transpose_bound μ T Ts hpq (Real.rpow_nonneg hbase _) hadj ?_ v hvp
  intro w hw
  have hb := operator_lp_below_two_of_weak_one_one μ Ts hcT hC hweak w hq1 hq2 hw
  rw [ENNReal.ofReal_rpow_of_nonneg hbase (div_nonneg (by norm_num) hpq.symm.nonneg)] at hb
  exact hb

end RothschildStein.H2

-- Copyright (c) 2026 Scott Armstrong and Amélie Loher. All rights reserved.
-- Released under Apache 2.0 license as described in the file LICENSE.
module

public import HeatKernel.Poincare.ChainOscillation
public import HeatKernel.Poincare.PowerIntegralBound

/-! Power-integral oscillation estimates along simple intersection paths. -/

@[expose] public section
set_option autoImplicit false
set_option relaxedAutoImplicit false
noncomputable section
open Set MeasureTheory
open scoped ENNReal BigOperators Classical

namespace HeatKernel

/-- The simple-path oscillation estimate gives a local power-integral bound before
any global integrability of the oscillation has been established. -/
theorem lintegral_abs_sub_rpow_le_simple_path_cost {E ι : Type*} [MeasurableSpace E]
    (μ : Measure E) (f : E → ℝ) (U : Set E) (G : SimpleGraph ι)
    (c e : ι → ℝ) (he : ∀ k, 0 ≤ e k) {K : ℝ} (hK : 0 ≤ K)
    (hstep : ∀ k l, G.Adj k l → |c k - c l| ≤ K * (e k + e l))
    {i j : ι} (w : G.Walk i j) (hw : w.IsPath) {p : ℝ} (hp : 1 ≤ p)
    (hf : AEStronglyMeasurable (fun x => f x - c j) (μ.restrict U))
    (hlocal : eLpNorm (fun x => f x - c i) (ENNReal.ofReal p) (μ.restrict U) ≤
      ENNReal.ofReal (K * e i) * μ U ^ (1 / p)) :
    (∫⁻ x in U, ENNReal.ofReal (|f x - c j| ^ p) ∂μ) ≤
      ENNReal.ofReal ((3 * K) ^ p) * μ U *
        ENNReal.ofReal ((∑ k ∈ w.support.toFinset, e k) ^ p) := by
  have hp0 : 0 < p := lt_of_lt_of_le zero_lt_one hp
  have hK3 : 0 ≤ 3 * K := mul_nonneg (by norm_num) hK
  have hS : 0 ≤ ∑ k ∈ w.support.toFinset, e k := Finset.sum_nonneg (fun k _ => he k)
  have hn := eLpNorm_sub_le_three_mul_simple_path_cost μ f U G c e he hK hstep w hw
    (show 1 ≤ ENNReal.ofReal p by
      simpa only [ENNReal.ofReal_one] using (ENNReal.ofReal_le_ofReal hp))
    ENNReal.ofReal_ne_top
    (by simpa only [ENNReal.toReal_ofReal hp0.le] using hlocal)
  rw [ENNReal.toReal_ofReal hp0.le] at hn
  have hi := lintegral_abs_rpow_le_of_eLpNorm_le hp0 (mul_nonneg hK3 hS) hf
    (by simpa only [Measure.restrict_apply_univ] using hn)
  rw [Real.mul_rpow hK3 hS, ENNReal.ofReal_mul (Real.rpow_nonneg hK3 _)] at hi
  rw [Measure.restrict_apply_univ] at hi
  calc
    _ ≤ _ := hi
    _ = _ := by ac_rfl

end HeatKernel

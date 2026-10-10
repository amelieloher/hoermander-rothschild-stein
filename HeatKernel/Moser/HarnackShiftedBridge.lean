-- Copyright (c) 2026 Scott Armstrong and Amélie Loher. All rights reserved.
-- Released under Apache 2.0 license as described in the file LICENSE.
module

public import Mathlib.MeasureTheory.Function.EssSup
public import Mathlib.Analysis.SpecificLimits.Basic
public import Mathlib.Analysis.Complex.Exponential
import Mathlib.Tactic

/-! # Cancellation of logarithmic shifts in the Harnack bridge

Two normalized bounds with the same exponential shift give a comparison independent
of that shift. Countably many positive perturbations suffice to remove the perturbation
on a common full-measure set. The estimates supplying the normalized bounds remain
explicit hypotheses.
-/

@[expose] public section
set_option autoImplicit false
set_option relaxedAutoImplicit false
noncomputable section
open MeasureTheory Filter
open scoped ENNReal Topology
namespace HeatKernel

/-- The common logarithmic shift cancels between the earlier upper bound and the
later reciprocal bound. -/
theorem le_mul_of_shifted_reciprocal_bounds {u v c ε Cminus Cplus : ℝ}
    (hCminus : 0 ≤ Cminus) (hv : 0 < v + ε)
    (hu : Real.exp (-c) * (u + ε) ≤ Cminus)
    (hrecip : Real.exp c / (v + ε) ≤ Cplus) :
    u + ε ≤ (Cminus * Cplus) * (v + ε) := by
  have hupper : u + ε ≤ Cminus * Real.exp c := by
    have h := mul_le_mul_of_nonneg_left hu (Real.exp_pos c).le
    rw [← mul_assoc, ← Real.exp_add, add_neg_cancel, Real.exp_zero, one_mul] at h
    simpa only [mul_comm] using h
  have hlower : Real.exp c ≤ Cplus * (v + ε) := (div_le_iff₀ hv).mp hrecip
  exact hupper.trans (by simpa only [mul_assoc] using
    mul_le_mul_of_nonneg_left hlower hCminus)

/-- Uniform normalized bounds for every positive perturbation yield an almost
everywhere comparison of the unperturbed earlier and later functions. The shift
may depend on the perturbation. -/
theorem ae_comparison_of_shifted_reciprocal_bounds {α β : Type*}
    [MeasurableSpace α] [MeasurableSpace β] {μ : Measure α} {ν : Measure β}
    {u : α → ℝ} {v : β → ℝ} {Cminus Cplus : ℝ} (hCminus : 0 ≤ Cminus)
    (hv : ∀ᵐ y ∂ν, 0 ≤ v y)
    (hbounds : ∀ ε : ℝ, 0 < ε → ∃ c : ℝ,
      (∀ᵐ x ∂μ, Real.exp (-c) * (u x + ε) ≤ Cminus) ∧
      (∀ᵐ y ∂ν, Real.exp c / (v y + ε) ≤ Cplus)) :
    ∀ᵐ x ∂μ, ∀ᵐ y ∂ν, u x ≤ (Cminus * Cplus) * v y := by
  have hn : ∀ n : ℕ, ∀ᵐ x ∂μ, ∀ᵐ y ∂ν,
      u x + (1 / 2 : ℝ) ^ n ≤ (Cminus * Cplus) * (v y + (1 / 2 : ℝ) ^ n) := by
    intro n
    have hε : 0 < (1 / 2 : ℝ) ^ n := pow_pos (by norm_num) n
    obtain ⟨c, hu, hrecip⟩ := hbounds _ hε
    filter_upwards [hu] with x hx
    filter_upwards [hv, hrecip] with y hy hrecipy
    exact le_mul_of_shifted_reciprocal_bounds hCminus (by linarith) hx hrecipy
  have hall : ∀ᵐ x ∂μ, ∀ n : ℕ, ∀ᵐ y ∂ν,
      u x + (1 / 2 : ℝ) ^ n ≤ (Cminus * Cplus) * (v y + (1 / 2 : ℝ) ^ n) :=
    ae_all_iff.mpr hn
  have hzero : Tendsto (fun n : ℕ => (1 / 2 : ℝ) ^ n) atTop (𝓝 0) :=
    tendsto_pow_atTop_nhds_zero_of_lt_one (by norm_num) (by norm_num)
  filter_upwards [hall] with x hx
  filter_upwards [ae_all_iff.mpr hx] with y hy
  exact le_of_tendsto_of_tendsto'
    (by simpa only [add_zero] using tendsto_const_nhds.add hzero)
    (by simpa only [add_zero] using (tendsto_const_nhds.add hzero).const_mul (Cminus * Cplus)) hy

/-- Almost everywhere real comparisons give the extended nonnegative Harnack
inequality directly. A positive finite constant permits division before taking the
essential infimum, without a real essential boundedness assumption. -/
theorem essSup_ofReal_le_mul_essInf_ofReal_of_ae_comparison {α β : Type*}
    [MeasurableSpace α] [MeasurableSpace β] {μ : Measure α} {ν : Measure β}
    {u : α → ℝ} {v : β → ℝ} {H : ℝ} (hH : 0 < H)
    (h : ∀ᵐ x ∂μ, ∀ᵐ y ∂ν, u x ≤ H * v y) :
    essSup (fun x => ENNReal.ofReal (u x)) μ ≤
      ENNReal.ofReal H * essInf (fun y => ENNReal.ofReal (v y)) ν := by
  have hH₀ : ENNReal.ofReal H ≠ 0 := (ENNReal.ofReal_pos.mpr hH).ne'
  refine essSup_le_of_ae_le _ ?_ (by isBoundedDefault)
  filter_upwards [h] with x hx
  have hlower : ENNReal.ofReal (u x) / ENNReal.ofReal H ≤
      essInf (fun y => ENNReal.ofReal (v y)) ν := by
    refine le_essInf_of_ae_le _ ?_ (by isBoundedDefault)
    filter_upwards [hx] with y hy
    apply (ENNReal.div_le_iff hH₀ ENNReal.ofReal_ne_top).mpr
    simpa only [ENNReal.ofReal_mul hH.le, mul_comm] using ENNReal.ofReal_le_ofReal hy
  simpa only [mul_comm] using
    (ENNReal.div_le_iff hH₀ ENNReal.ofReal_ne_top).mp hlower

/-- The perturbation limit and shift cancellation give the literal extended
nonnegative essential-extremum inequality. -/
theorem essSup_ofReal_le_mul_essInf_ofReal_of_shifted_reciprocal_bounds {α β : Type*}
    [MeasurableSpace α] [MeasurableSpace β] {μ : Measure α} {ν : Measure β}
    {u : α → ℝ} {v : β → ℝ} {Cminus Cplus : ℝ} (hCminus : 0 < Cminus) (hCplus : 0 < Cplus)
    (hv : ∀ᵐ y ∂ν, 0 ≤ v y)
    (hbounds : ∀ ε : ℝ, 0 < ε → ∃ c : ℝ,
      (∀ᵐ x ∂μ, Real.exp (-c) * (u x + ε) ≤ Cminus) ∧
      (∀ᵐ y ∂ν, Real.exp c / (v y + ε) ≤ Cplus)) :
    essSup (fun x => ENNReal.ofReal (u x)) μ ≤
      ENNReal.ofReal (Cminus * Cplus) * essInf (fun y => ENNReal.ofReal (v y)) ν :=
  essSup_ofReal_le_mul_essInf_ofReal_of_ae_comparison (mul_pos hCminus hCplus)
    (ae_comparison_of_shifted_reciprocal_bounds hCminus.le hv hbounds)

end HeatKernel

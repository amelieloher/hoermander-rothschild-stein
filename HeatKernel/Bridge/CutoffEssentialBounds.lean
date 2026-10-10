-- Copyright (c) 2026 Scott Armstrong and Amélie Loher. All rights reserved.
-- Released under Apache 2.0 license as described in the file LICENSE.
module

public import HeatKernel.Form.EssentialSpatialBounds
public import Mathlib.MeasureTheory.Function.LpSeminorm.Indicator
public import Mathlib.MeasureTheory.Function.LpSeminorm.Monotonicity
import Mathlib.Tactic

/-! # Essential spatial L² bounds of cutoff representatives -/

@[expose] public section
open Set MeasureTheory
open scoped ENNReal
namespace HeatKernel

/-- Multiplication by a bounded spatial cutoff preserves the essential spatial L²
bound for any curve representing that product almost everywhere. -/
theorem essSup_eLpNorm_cutoff_rep_le {α β : Type*}
    [MeasurableSpace α] [MeasurableSpace β] {μ : Measure α} {ν : Measure β}
    {K : Set β} (hK : MeasurableSet K) (u : α → β → ℝ)
    {φ : β → ℝ} {C : ℝ} (hφ : ∀ x, ‖φ x‖ ≤ C) (hs : Function.support φ ⊆ K)
    (v : α → Lp ℝ 2 ν)
    (hv : ∀ᵐ t ∂μ, (v t : β → ℝ) =ᵐ[ν] fun x => u t x * φ x) :
    essSup (fun t => eLpNorm (v t : β → ℝ) 2 ν) μ ≤
      ENNReal.ofReal C * essSup (fun t => eLpNorm (u t) 2 (ν.restrict K)) μ := by
  refine essSup_le_of_ae_le _ ?_
  filter_upwards [hv, ENNReal.ae_le_essSup (μ := μ)
    (fun t => eLpNorm (u t) 2 (ν.restrict K))] with t ht hb
  have hm : AEStronglyMeasurable (fun x => u t x * φ x) ν :=
    (Lp.memLp (v t)).aestronglyMeasurable.congr ht
  have hp : ∀ᵐ x ∂ν, ‖u t x * φ x‖ ≤ C * ‖K.indicator (u t) x‖ := by
    filter_upwards [] with x
    by_cases hx : x ∈ K
    · rw [indicator_of_mem hx, norm_mul, mul_comm C]
      exact mul_le_mul_of_nonneg_left (hφ x) (norm_nonneg _)
    · have hz : φ x = 0 := by
        by_contra hn
        exact hx (hs hn)
      simp [hz, indicator_of_notMem hx]
  have H := eLpNorm_le_mul_eLpNorm_of_ae_le_mul hm hp 2
  rw [eLpNorm_indicator_eq_eLpNorm_restrict hK] at H
  rw [eLpNorm_congr_ae ht]
  exact H.trans (mul_le_mul' le_rfl hb)

/-- Finite essential spatial L² bounds remain finite after bounded cutoff multiplication. -/
theorem essSup_eLpNorm_cutoff_rep_lt_top {α β : Type*}
    [MeasurableSpace α] [MeasurableSpace β] {μ : Measure α} {ν : Measure β}
    {K : Set β} (hK : MeasurableSet K) (u : α → β → ℝ)
    {φ : β → ℝ} {C : ℝ} (hφ : ∀ x, ‖φ x‖ ≤ C) (hs : Function.support φ ⊆ K)
    (v : α → Lp ℝ 2 ν)
    (hv : ∀ᵐ t ∂μ, (v t : β → ℝ) =ᵐ[ν] fun x => u t x * φ x)
    (hb : essSup (fun t => eLpNorm (u t) 2 (ν.restrict K)) μ < ⊤) :
    essSup (fun t => eLpNorm (v t : β → ℝ) 2 ν) μ < ⊤ :=
  (essSup_eLpNorm_cutoff_rep_le hK u hφ hs v hv).trans_lt
    (ENNReal.mul_lt_top ENNReal.ofReal_lt_top hb)

end HeatKernel

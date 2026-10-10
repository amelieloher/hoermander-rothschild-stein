-- Copyright (c) 2026 Scott Armstrong and Amélie Loher. All rights reserved.
-- Released under Apache 2.0 license as described in the file LICENSE.
module

public import HeatKernel.Moser.OscillationContraction

/-! # Essential Harnack estimates and oscillation

Essential extrema of the two nonnegative shifts yield almost everywhere comparisons,
which give a quantitative contraction of the essential oscillation.
-/

@[expose] public section

open MeasureTheory Filter

namespace HeatKernel

/-- An extended nonnegative Harnack estimate gives real almost everywhere comparisons
without any boundedness assumption on the earlier function. -/
theorem ae_comparison_of_ofReal_harnack {α β : Type*}
    [MeasurableSpace α] [MeasurableSpace β] {μ : Measure α} {ν : Measure β}
    {u : α → ℝ} {v : β → ℝ} {H : ℝ} (hH : 0 ≤ H)
    (hu : ∀ᵐ x ∂μ, 0 ≤ u x) (hv : ∀ᵐ y ∂ν, 0 ≤ v y)
    (h : essSup (fun x => ENNReal.ofReal (u x)) μ ≤
      ENNReal.ofReal H * essInf (fun y => ENNReal.ofReal (v y)) ν) :
    ∀ᵐ x ∂μ, ∀ᵐ y ∂ν, u x ≤ H * v y := by
  filter_upwards [hu, ae_le_essSup (μ := μ) (f := fun x => ENNReal.ofReal (u x))]
    with x hx hxs
  filter_upwards [hv, ae_essInf_le (μ := ν) (f := fun y => ENNReal.ofReal (v y))]
    with y hy hys
  have he : ENNReal.ofReal (u x) ≤ ENNReal.ofReal (H * v y) := by
    rw [ENNReal.ofReal_mul hH]
    exact hxs.trans (h.trans (mul_le_mul_of_nonneg_left hys bot_le))
  simpa only [ENNReal.toReal_ofReal hx, ENNReal.toReal_ofReal (mul_nonneg hH hy)] using
    ENNReal.toReal_mono ENNReal.ofReal_ne_top he

/-- Harnack estimates in extended nonnegative essential extrema give a real essential
oscillation bound for a bounded later function. -/
theorem essSup_sub_essInf_le_of_shifted_ofReal_harnack {α β : Type*}
    [MeasurableSpace α] [MeasurableSpace β] {μ : Measure α} {ν : Measure β}
    {u : α → ℝ} {v : β → ℝ} {m M H : ℝ} (hμ : μ ≠ 0) (hν : ν ≠ 0)
    (hH : 0 < H) (hu : ∀ᵐ x ∂μ, m ≤ u x ∧ u x ≤ M)
    (hv : ∀ᵐ y ∂ν, m ≤ v y ∧ v y ≤ M)
    (hl : essSup (fun x => ENNReal.ofReal (u x - m)) μ ≤ ENNReal.ofReal H *
      essInf (fun y => ENNReal.ofReal (v y - m)) ν)
    (hr : essSup (fun x => ENNReal.ofReal (M - u x)) μ ≤ ENNReal.ofReal H *
      essInf (fun y => ENNReal.ofReal (M - v y)) ν) :
    essSup v ν - essInf v ν ≤ (1 - 1 / (2 * H)) * (M - m) := by
  have hlc := ae_comparison_of_ofReal_harnack hH.le
    (hu.mono fun _ h => sub_nonneg.mpr h.1)
    (hv.mono fun _ h => sub_nonneg.mpr h.1) hl
  have hrc := ae_comparison_of_ofReal_harnack hH.le
    (hu.mono fun _ h => sub_nonneg.mpr h.2)
    (hv.mono fun _ h => sub_nonneg.mpr h.2) hr
  apply essSup_sub_essInf_le_of_shifted_harnack_comparisons hμ hν hH hv
  filter_upwards [hlc, hrc] with x hx hy
  exact ⟨hx, hy⟩

end HeatKernel

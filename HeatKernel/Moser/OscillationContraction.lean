-- Copyright (c) 2026 Scott Armstrong and Amélie Loher. All rights reserved.
-- Released under Apache 2.0 license as described in the file LICENSE.
module

public import Mathlib

/-! # Oscillation contraction from shifted Harnack comparisons

Applying Harnack to both shifts of a bounded solution gives a uniform loss in its
oscillation. The comparison hypotheses below isolate the analytic input.
-/

@[expose] public section

open MeasureTheory Filter

namespace HeatKernel

/-- The contraction factor associated with a Harnack constant is strictly between zero and one. -/
theorem harnack_oscillation_factor_mem_Ioo {H : ℝ} (hH : 1 ≤ H) :
    1 - 1 / (2 * H) ∈ Set.Ioo (0 : ℝ) 1 := by
  have hpos : 0 < 2 * H := by linarith
  have hsmall : 1 / (2 * H) ≤ 1 / 2 := by
    apply (div_le_iff₀ hpos).2
    linarith
  have hlarge : 0 < 1 / (2 * H) := div_pos one_pos hpos
  constructor <;> linarith

/-- Two shifted Harnack comparisons reduce the difference between any two later values. -/
theorem abs_sub_le_of_shifted_harnack_comparisons {m M a b c H : ℝ}
    (hH : 0 < H) (hb : m ≤ b ∧ b ≤ M) (hc : m ≤ c ∧ c ≤ M)
    (hl : a - m ≤ H * (b - m) ∧ a - m ≤ H * (c - m))
    (hu : M - a ≤ H * (M - b) ∧ M - a ≤ H * (M - c)) :
    |b - c| ≤ (1 - 1 / (2 * H)) * (M - m) := by
  have hden : 0 < 2 * H := mul_pos (by norm_num) hH
  have heq : (1 - 1 / (2 * H)) * (M - m) =
      (M - m) - (M - m) / (2 * H) := by ring
  rw [heq, abs_sub_le_iff]
  by_cases hhalf : (M - m) / 2 ≤ a - m
  · have hb' : (M - m) / (2 * H) ≤ b - m := by
      apply (div_le_iff₀ hden).2
      nlinarith [hl.1]
    have hc' : (M - m) / (2 * H) ≤ c - m := by
      apply (div_le_iff₀ hden).2
      nlinarith [hl.2]
    constructor <;> linarith [hb.2, hc.2]
  · have hhalf' : (M - m) / 2 ≤ M - a := by linarith
    have hb' : (M - m) / (2 * H) ≤ M - b := by
      apply (div_le_iff₀ hden).2
      nlinarith [hu.1]
    have hc' : (M - m) / (2 * H) ≤ M - c := by
      apply (div_le_iff₀ hden).2
      nlinarith [hu.2]
    constructor <;> linarith [hb.1, hc.1]

/-- Almost everywhere shifted Harnack comparisons on two nonempty measure regions give
an almost everywhere oscillation bound on the later region. -/
theorem ae_abs_sub_le_of_shifted_harnack_comparisons {α β : Type*}
    [MeasurableSpace α] [MeasurableSpace β] {μ : Measure α} {ν : Measure β}
    {u : α → ℝ} {v : β → ℝ} {m M H : ℝ} (hμ : μ ≠ 0) (hH : 0 < H)
    (hv : ∀ᵐ y ∂ν, m ≤ v y ∧ v y ≤ M)
    (hcomp : ∀ᵐ x ∂μ,
      (∀ᵐ y ∂ν, u x - m ≤ H * (v y - m)) ∧
      (∀ᵐ y ∂ν, M - u x ≤ H * (M - v y))) :
    ∀ᵐ y ∂ν, ∀ᵐ z ∂ν,
      |v y - v z| ≤ (1 - 1 / (2 * H)) * (M - m) := by
  have : (ae μ).NeBot := ae_neBot.mpr hμ
  obtain ⟨x, hx⟩ := hcomp.exists
  filter_upwards [hv, hx.1, hx.2] with y hy hly huy
  filter_upwards [hv, hx.1, hx.2] with z hz hlz huz
  exact abs_sub_le_of_shifted_harnack_comparisons hH hy hz ⟨hly, hlz⟩ ⟨huy, huz⟩

/-- An almost everywhere pairwise difference bound controls the essential oscillation
of a bounded real function on a nonzero measure space. -/
theorem essSup_sub_essInf_le_of_ae_abs_sub_le {α : Type*} [MeasurableSpace α]
    {μ : Measure α} {v : α → ℝ} {m M C : ℝ} (hμ : μ ≠ 0)
    (hv : ∀ᵐ y ∂μ, m ≤ v y ∧ v y ≤ M)
    (hpair : ∀ᵐ y ∂μ, ∀ᵐ z ∂μ, |v y - v z| ≤ C) :
    essSup v μ - essInf v μ ≤ C := by
  have : (ae μ).NeBot := ae_neBot.mpr hμ
  have hlo : IsCoboundedUnder (· ≤ ·) (ae μ) v :=
    .of_frequently_ge (hv.mono fun _ h => h.1).frequently
  have hhi : IsCoboundedUnder (· ≥ ·) (ae μ) v :=
    .of_frequently_le (hv.mono fun _ h => h.2).frequently
  have hup : ∀ᵐ y ∂μ, v y ≤ C + essInf v μ := by
    filter_upwards [hpair] with y hy
    have hi : v y - C ≤ essInf v μ := by
      apply le_essInf_of_ae_le _ _ hhi
      filter_upwards [hy] with z hz
      have h := (abs_le.mp hz).2
      linarith
    linarith
  have hs := essSup_le_of_ae_le (C + essInf v μ) hup hlo
  linarith

/-- Shifted Harnack comparisons reduce the essential oscillation on the later region. -/
theorem essSup_sub_essInf_le_of_shifted_harnack_comparisons {α β : Type*}
    [MeasurableSpace α] [MeasurableSpace β] {μ : Measure α} {ν : Measure β}
    {u : α → ℝ} {v : β → ℝ} {m M H : ℝ} (hμ : μ ≠ 0) (hν : ν ≠ 0)
    (hH : 0 < H) (hv : ∀ᵐ y ∂ν, m ≤ v y ∧ v y ≤ M)
    (hcomp : ∀ᵐ x ∂μ,
      (∀ᵐ y ∂ν, u x - m ≤ H * (v y - m)) ∧
      (∀ᵐ y ∂ν, M - u x ≤ H * (M - v y))) :
    essSup v ν - essInf v ν ≤ (1 - 1 / (2 * H)) * (M - m) := by
  exact essSup_sub_essInf_le_of_ae_abs_sub_le hν hv
    (ae_abs_sub_le_of_shifted_harnack_comparisons hμ hH hv hcomp)

end HeatKernel

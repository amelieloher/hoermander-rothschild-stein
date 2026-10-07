-- Copyright (c) 2026 Scott Armstrong and Amélie Loher. All rights reserved.
-- Released under Apache 2.0 license as described in the file LICENSE.
module

public import RothschildStein.G4.VolumePolynomial
public import Mathlib.MeasureTheory.Measure.Basic
public import Mathlib.Analysis.SpecialFunctions.Pow.NNReal

@[expose] public section
set_option autoImplicit false
set_option relaxedAutoImplicit false
noncomputable section
open Set MeasureTheory
open scoped ENNReal

namespace RothschildStein.G4

/-- The volume-polynomial comparison implies the exact fixed-factor
measure bound, with both radii inside the theorem's range
(BB Thm 9.1, p. 400). -/
theorem measure_scale_le_of_volumePolynomial_bounds {ι α : Type*} [Fintype ι]
    [MeasurableSpace α] (μ : Measure α) (B : ℝ → Set α) (lam : ι → ℝ) (w : ι → ℕ)
    {D : ℕ} (hw : ∀ i, w i ≤ D) {c C r₀ : ℝ} (hc : 0 < c) (hC : 0 ≤ C)
    (hvol : ∀ r, 0 < r → r ≤ r₀ →
      ENNReal.ofReal (c * volumePolynomial lam w r) ≤ μ (B r) ∧
      μ (B r) ≤ ENNReal.ofReal (C * volumePolynomial lam w r))
    {A r : ℝ} (hA : 1 ≤ A) (hr : 0 < r) (hAr : A * r ≤ r₀) :
    μ (B (A * r)) ≤ ENNReal.ofReal ((C / c) * A ^ D) * μ (B r) := by
  have hA0 : 0 < A := zero_lt_one.trans_le hA
  have hrr₀ : r ≤ r₀ := (le_mul_of_one_le_left hr.le hA).trans hAr
  obtain ⟨hlo, hhi⟩ := hvol r hr hrr₀
  obtain ⟨_, hhiA⟩ := hvol (A * r) (mul_pos hA0 hr) hAr
  have hfin : μ (B r) ≠ ∞ := ne_top_of_le_ne_top ENNReal.ofReal_ne_top hhi
  have hfinA : μ (B (A * r)) ≠ ∞ := ne_top_of_le_ne_top ENNReal.ofReal_ne_top hhiA
  have hlow : c * volumePolynomial lam w r ≤ (μ (B r)).toReal := by
    simpa only [ENNReal.toReal_ofReal (mul_nonneg hc.le (volumePolynomial_nonneg lam w hr.le))] using
      ENNReal.toReal_mono hfin hlo
  have hupp : (μ (B (A * r))).toReal ≤ C * volumePolynomial lam w (A * r) := by
    simpa only [ENNReal.toReal_ofReal (mul_nonneg hC
      (volumePolynomial_nonneg lam w (mul_nonneg hA0.le hr.le)))] using
      ENNReal.toReal_mono ENNReal.ofReal_ne_top hhiA
  have hscale := mul_le_mul_of_nonneg_left (volumePolynomial_scale_le lam w hw hA hr.le) hC
  have hbound : (μ (B (A * r))).toReal ≤ ((C / c) * A ^ D) * (μ (B r)).toReal := by
    have h := mul_le_mul_of_nonneg_left hlow (div_nonneg (mul_nonneg hC (pow_nonneg hA0.le D)) hc.le)
    have heq : (C * A ^ D / c) * (c * volumePolynomial lam w r) =
        C * (A ^ D * volumePolynomial lam w r) := by field_simp
    rw [heq] at h
    have heq' : C * A ^ D / c = (C / c) * A ^ D := by ring
    exact (hupp.trans hscale).trans (by simpa only [heq'] using h)
  have hm := ENNReal.ofReal_le_ofReal hbound
  rwa [ENNReal.ofReal_toReal hfinA,
    ENNReal.ofReal_mul (mul_nonneg (div_nonneg hC hc.le) (pow_nonneg hA0.le D)),
    ENNReal.ofReal_toReal hfin] at hm

/-- Volume-polynomial comparison gives positive finite ball measure
whenever one frame is nonzero (BB Thms 9.1/9.12, pp. 400, 405). -/
theorem measure_pos_finite_of_volumePolynomial_bounds {ι α : Type*} [Fintype ι]
    [MeasurableSpace α] (μ : Measure α) (B : Set α) (lam : ι → ℝ) (w : ι → ℕ)
    {c C r : ℝ} (hc : 0 < c) (hr : 0 < r) (i : ι) (hi : lam i ≠ 0)
    (hlo : ENNReal.ofReal (c * volumePolynomial lam w r) ≤ μ B)
    (hhi : μ B ≤ ENNReal.ofReal (C * volumePolynomial lam w r)) : 0 < μ B ∧ μ B < ∞ :=
  ⟨(ENNReal.ofReal_pos.mpr (mul_pos hc (volumePolynomial_pos lam w hr i hi))).trans_le hlo,
    hhi.trans_lt ENNReal.ofReal_lt_top⟩

end RothschildStein.G4

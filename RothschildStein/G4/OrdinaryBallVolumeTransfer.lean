-- Copyright (c) 2026 Scott Armstrong and Amélie Loher. All rights reserved.
-- Released under Apache 2.0 license as described in the file LICENSE.
module

public import RothschildStein.G4.VolumeDoubling

@[expose] public section
set_option autoImplicit false
set_option relaxedAutoImplicit false
noncomputable section
open Set MeasureTheory
open scoped ENNReal
namespace RothschildStein.G4

/-- The original-radius polynomial lower bound survives the
radius loss in ordinary/auxiliary ball equivalence (BB p. 405). -/
theorem volumePolynomial_shrink_lower {ι : Type*} [Fintype ι]
    (lam : ι → ℝ) (w : ι → ℕ) {D : ℕ} (hw : ∀ i, w i ≤ D)
    {A r : ℝ} (hA : 1 ≤ A) (hr : 0 ≤ r) :
    volumePolynomial lam w r / A ^ D ≤ volumePolynomial lam w (r / A) := by
  have hAp : 0 < A := zero_lt_one.trans_le hA
  have he : A * (r / A) = r := by field_simp
  have hb := volumePolynomial_scale_le lam w hw hA (div_nonneg hr hAp.le)
  rw [he] at hb
  exact (div_le_iff₀ (pow_pos hAp D)).mpr (by simpa only [mul_comm] using hb)

/-- Transfer the two genuine auxiliary-ball volume bounds
through the ball sandwich. The radius loss appears explicitly in the
lower constant; no volume bound for the ordinary ball is assumed. -/
theorem ordinary_ball_volume_bounds_of_ball_sandwich
    {ι E : Type*} [Fintype ι] [MeasurableSpace E]
    (μ : Measure E) (Ba Bo : ℝ → Set E)
    (lam : ι → ℝ) (w : ι → ℕ) {D : ℕ} (hw : ∀ i, w i ≤ D)
    {A c C ε r : ℝ} (hA : 1 ≤ A) (hc : 0 < c)
    (hr : 0 < r) (hrr : r ≤ ε)
    (haux : ∀ t, 0 < t → t ≤ ε →
      ENNReal.ofReal (c * volumePolynomial lam w t) ≤ μ (Ba t) ∧
      μ (Ba t) ≤ ENNReal.ofReal (C * volumePolynomial lam w t))
    (hballs : Ba (r / A) ⊆ Bo r ∧ Bo r ⊆ Ba r) :
    ENNReal.ofReal ((c / A ^ D) * volumePolynomial lam w r) ≤ μ (Bo r) ∧
      μ (Bo r) ≤ ENNReal.ofReal (C * volumePolynomial lam w r) := by
  have hAp : 0 < A := zero_lt_one.trans_le hA
  have hsmall : r / A ≤ ε := (div_le_self hr.le hA).trans hrr
  constructor
  · calc
      _ ≤ ENNReal.ofReal (c * volumePolynomial lam w (r / A)) := by
        apply ENNReal.ofReal_le_ofReal
        have hh := mul_le_mul_of_nonneg_left (volumePolynomial_shrink_lower lam w hw hA hr.le) hc.le
        simpa only [div_mul_eq_mul_div, mul_div_assoc] using hh
      _ ≤ μ (Ba (r / A)) := (haux _ (div_pos hr hAp) hsmall).1
      _ ≤ μ (Bo r) := measure_mono hballs.1
  · exact (measure_mono hballs.2).trans (haux r hr hrr).2

end RothschildStein.G4

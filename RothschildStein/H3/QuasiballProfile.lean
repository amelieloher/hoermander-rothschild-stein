-- Copyright (c) 2026 Scott Armstrong and Amélie Loher. All rights reserved.
-- Released under Apache 2.0 license as described in the file LICENSE.
module

public import Mathlib.Analysis.SpecialFunctions.SmoothTransition

set_option autoImplicit false
set_option relaxedAutoImplicit false
@[expose] public section
noncomputable section
namespace RothschildStein.H3

/-- The smooth profile used between radii t and (t+s)/2
(BB Lemma 8.40, p. 370). -/
def quasiballProfile (t s ρ : ℝ) : ℝ :=
  Real.smoothTransition (((t + s) / 2 - ρ) / ((s - t) / 2))

/-- The profile takes values between zero and one. -/
theorem quasiballProfile_range (t s ρ : ℝ) :
    0 ≤ quasiballProfile t s ρ ∧ quasiballProfile t s ρ ≤ 1 :=
  ⟨Real.smoothTransition.nonneg _, Real.smoothTransition.le_one _⟩

/-- The profile equals one at and below the inner radius. -/
theorem quasiballProfile_one {t s ρ : ℝ} (hts : t < s) (hρ : ρ ≤ t) :
    quasiballProfile t s ρ = 1 := by
  apply Real.smoothTransition.one_of_one_le
  apply (le_div_iff₀ (by linarith : 0 < (s - t) / 2)).mpr
  linarith

/-- The profile vanishes at and beyond the intermediate radius. -/
theorem quasiballProfile_zero {t s ρ : ℝ} (hts : t < s) (hρ : (t + s) / 2 ≤ ρ) :
    quasiballProfile t s ρ = 0 := by
  apply Real.smoothTransition.zero_of_nonpos
  exact div_nonpos_of_nonpos_of_nonneg (sub_nonpos.mpr hρ) (by linarith)

/-- The scalar profile is smooth for all fixed radii. -/
theorem quasiballProfile_contDiff (t s : ℝ) :
    ContDiff ℝ (⊤ : ℕ∞) (quasiballProfile t s) :=
  Real.smoothTransition.contDiff.comp
    ((contDiff_const.sub contDiff_id).div_const ((s - t) / 2))

end RothschildStein.H3

-- Copyright (c) 2026 Scott Armstrong and Amélie Loher. All rights reserved.
-- Released under Apache 2.0 license as described in the file LICENSE.
module

public import RothschildStein.L1.FiberDensityRatio

/-!
# Fixed-factor rescaling: scale algebra

Pure real/ENNReal bookkeeping for the corrected fixed-factor rescaling of the
fiber bounds (BB pp. 521–522): the transfer of
ENNReal quotient inequalities of ball volumes to the real quotients of
`GaugeFiberData.ball_bounds`, and the explicit choice of the fixed enlargement
factors and the radius threshold.
-/

@[expose] public section
set_option autoImplicit false
set_option relaxedAutoImplicit false
noncomputable section
open Set MeasureTheory
open scoped ENNReal
namespace RothschildStein.L1

/-- An upper ENNReal quotient comparison of finite ball volumes with a
positive original volume gives the same comparison of the real quotients
(BB pp. 521–522). -/
theorem fiberRescaling_real_ratio_le {n N : ℕ} {U₁ U₀ : Set (Fin N → ℝ)}
    {V₁ V₀ : Set (Fin n → ℝ)} (hU₁ : volume U₁ ≠ ⊤) (hU₀ : volume U₀ ≠ ⊤)
    (hV₁ : volume V₁ ≠ ⊤) (hV₀ : volume V₀ ≠ ⊤)
    (hV₁pos : 0 < (volume V₁).toReal) (hV₀pos : 0 < (volume V₀).toReal)
    {c : ℝ} (hc : 0 ≤ c)
    (h : volume U₁ / volume V₁ ≤ ENNReal.ofReal c * (volume U₀ / volume V₀)) :
    (volume U₁).toReal / (volume V₁).toReal ≤
      c * ((volume U₀).toReal / (volume V₀).toReal) := by
  rw [← ofReal_volume_toReal_ratio V₁ U₁ hV₁ hU₁ hV₁pos,
    ← ofReal_volume_toReal_ratio V₀ U₀ hV₀ hU₀ hV₀pos, ← ENNReal.ofReal_mul hc] at h
  exact (ENNReal.ofReal_le_ofReal_iff (mul_nonneg hc
    (div_nonneg ENNReal.toReal_nonneg ENNReal.toReal_nonneg))).1 h

/-- A lower ENNReal quotient comparison of finite ball volumes with a
positive original volume gives the same comparison of the real quotients
(BB pp. 521–522). -/
theorem fiberRescaling_real_ratio_ge {n N : ℕ} {U₁ U₀ : Set (Fin N → ℝ)}
    {V₁ V₀ : Set (Fin n → ℝ)} (hU₁ : volume U₁ ≠ ⊤) (hU₀ : volume U₀ ≠ ⊤)
    (hV₁ : volume V₁ ≠ ⊤) (hV₀ : volume V₀ ≠ ⊤)
    (hV₁pos : 0 < (volume V₁).toReal) (hV₀pos : 0 < (volume V₀).toReal)
    {c : ℝ} (hc : 0 ≤ c)
    (h : ENNReal.ofReal c * (volume U₀ / volume V₀) ≤ volume U₁ / volume V₁) :
    c * ((volume U₀).toReal / (volume V₀).toReal) ≤
      (volume U₁).toReal / (volume V₁).toReal := by
  rw [← ofReal_volume_toReal_ratio V₁ U₁ hV₁ hU₁ hV₁pos,
    ← ofReal_volume_toReal_ratio V₀ U₀ hV₀ hU₀ hV₀pos, ← ENNReal.ofReal_mul hc] at h
  exact (ENNReal.ofReal_le_ofReal_iff
    (div_nonneg ENNReal.toReal_nonneg ENNReal.toReal_nonneg)).1 h

/-- The fixed enlargement factors `Λ`, `Λ'`, the shrinking factor `δf` and
the radius threshold of the corrected fixed-factor rescaling. Every radius below the
threshold stays inside the validity ranges `r₁` (starred comparison), `rd` (ball density
facts), `r₀` (starred fiber bounds) and `rr` (volume-ratio rescaling), after enlargement
by `Λ` or `Λ'` (BB pp. 521–522, erratum L1-R11). -/
theorem fiberRescaling_exists_scales {r₀ cw cs cl r₁ C rr rd : ℝ}
    (hr₀ : 0 < r₀) (hcw : 0 < cw) (hcs : 0 < cs) (hcl : 0 < cl) (hr₁ : 0 < r₁)
    (hC : 1 ≤ C) (hrr : 0 < rr) (hrd : 0 < rd) :
    ∃ Λ Λ' δf rstar : ℝ, 1 ≤ Λ ∧ 1 ≤ Λ' ∧ 0 < δf ∧ δf < 1 ∧ 0 < rstar ∧
      C ≤ cw * Λ ∧ C ≤ cs * Λ ∧ C * cl ≤ Λ' ∧ C * δf * Λ' ≤ cw ∧
      ∀ r : ℝ, 0 < r → r < rstar →
        r ≤ r₁ ∧ cl * r ≤ r₁ ∧ r < rd ∧ Λ * r < rd ∧ Λ * r ≤ r₀ ∧ Λ * r ≤ rr ∧
          Λ' * r ≤ rr := by
  have hC0 : 0 < C := lt_of_lt_of_le one_pos hC
  set Λ : ℝ := max 1 (max (C / cw) (C / cs)) with hΛdef
  set Λ' : ℝ := max 1 (C * cl) with hΛ'def
  have hΛ : 1 ≤ Λ := le_max_left _ _
  have hΛ' : 1 ≤ Λ' := le_max_left _ _
  have hΛ0 : 0 < Λ := lt_of_lt_of_le one_pos hΛ
  have hΛ'0 : 0 < Λ' := lt_of_lt_of_le one_pos hΛ'
  set δf : ℝ := min (1 / 2) (cw / (Λ' * C)) with hδfdef
  have hδf0 : 0 < δf := lt_min (by norm_num) (div_pos hcw (mul_pos hΛ'0 hC0))
  have hδf1 : δf < 1 := lt_of_le_of_lt (min_le_left _ _) (by norm_num)
  set Λm : ℝ := max Λ Λ' with hΛmdef
  have hΛm : 0 < Λm := lt_of_lt_of_le hΛ0 (le_max_left _ _)
  refine ⟨Λ, Λ', δf, min (min r₁ (r₁ / cl)) (min (rd / Λm) (min (r₀ / Λm) (rr / Λm))),
    hΛ, hΛ', hδf0, hδf1, ?_, ?_, ?_, le_max_right _ _, ?_, ?_⟩
  · exact lt_min (lt_min hr₁ (div_pos hr₁ hcl)) (lt_min (div_pos hrd hΛm)
      (lt_min (div_pos hr₀ hΛm) (div_pos hrr hΛm)))
  · rw [← div_le_iff₀' hcw]
    exact le_trans (le_max_left _ _) (le_max_right _ _)
  · rw [← div_le_iff₀' hcs]
    exact le_trans (le_max_right _ _) (le_max_right _ _)
  · have h1 : δf ≤ cw / (Λ' * C) := min_le_right _ _
    rw [le_div_iff₀ (mul_pos hΛ'0 hC0)] at h1
    linarith
  · intro r hr hrs
    have hrs1 : r < r₁ := lt_of_lt_of_le hrs (le_trans (min_le_left _ _) (min_le_left _ _))
    have hrs2 : r < r₁ / cl :=
      lt_of_lt_of_le hrs (le_trans (min_le_left _ _) (min_le_right _ _))
    have hrs3 : r < rd / Λm :=
      lt_of_lt_of_le hrs (le_trans (min_le_right _ _) (min_le_left _ _))
    have hrs4 : r < r₀ / Λm := lt_of_lt_of_le hrs (le_trans (min_le_right _ _)
      (le_trans (min_le_right _ _) (min_le_left _ _)))
    have hrs5 : r < rr / Λm := lt_of_lt_of_le hrs (le_trans (min_le_right _ _)
      (le_trans (min_le_right _ _) (min_le_right _ _)))
    rw [lt_div_iff₀ hΛm] at hrs3 hrs4 hrs5
    rw [lt_div_iff₀ hcl] at hrs2
    have hΛle : Λ ≤ Λm := le_max_left _ _
    have hΛ'le : Λ' ≤ Λm := le_max_right _ _
    have e1 : Λ * r ≤ Λm * r := mul_le_mul_of_nonneg_right hΛle hr.le
    have e2 : Λ' * r ≤ Λm * r := mul_le_mul_of_nonneg_right hΛ'le hr.le
    refine ⟨hrs1.le, by linarith, by nlinarith, by nlinarith, by nlinarith, by nlinarith,
      by nlinarith⟩

end RothschildStein.L1

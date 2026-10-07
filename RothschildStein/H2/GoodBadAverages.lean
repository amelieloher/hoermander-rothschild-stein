-- Copyright (c) 2026 Scott Armstrong and Amélie Loher. All rights reserved.
-- Released under Apache 2.0 license as described in the file LICENSE.
module

public import RothschildStein.H2.MaximalLevelSets
public import RothschildStein.H2.BallMeasures

@[expose] public section
set_option autoImplicit false
set_option relaxedAutoImplicit false
noncomputable section
open Set MeasureTheory Metric
open scoped ENNReal

namespace RothschildStein.H2
variable {X : Type*} [MetricSpace X] [MeasurableSpace X] [BorelSpace X]

/-- Comparing averages on a ball and its fivefold dilation costs three doubling steps (BB Lemma 7.34, p. 323). -/
theorem DoublingPatch.laverage_ball_le_five (P : DoublingPatch X) {z : X}
    (hz : z ∈ P.S) {r : ℝ} (hr : 0 < r) (hrρ : r ≤ P.ρ) (f : X → ℝ) :
    (⨍⁻ y in ball z r, ‖f y‖ₑ ∂P.μ) ≤ ENNReal.ofReal P.C_D ^ 3 *
      (⨍⁻ y in ball z (5 * r), ‖f y‖ₑ ∂P.μ) := by
  have hv := P.doubling z hz r hr (by linarith [P.ρ_pos])
  have hw := P.doubling z hz (5 * r) (by positivity) (by linarith [P.ρ_pos])
  have hc := P.compare_pow hz hr (by positivity : 0 < 5 * r)
    (by linarith [P.ρ_pos] : 5 * r ≤ 6 * P.ρ) 3 (by norm_num; linarith)
  rw [setLAverage_eq, setLAverage_eq]
  apply (ENNReal.div_le_iff hv.1.ne' hv.2.1.ne).mpr
  calc
    _ ≤ ∫⁻ y in ball z (5 * r), ‖f y‖ₑ ∂P.μ :=
      lintegral_mono' (Measure.restrict_mono (ball_subset_ball (by linarith)) le_rfl) le_rfl
    _ = ((∫⁻ y in ball z (5 * r), ‖f y‖ₑ ∂P.μ) / P.μ (ball z (5 * r))) *
        P.μ (ball z (5 * r)) := (ENNReal.div_mul_cancel hw.1.ne' hw.2.1.ne).symm
    _ ≤ ((∫⁻ y in ball z (5 * r), ‖f y‖ₑ ∂P.μ) / P.μ (ball z (5 * r))) *
        (ENNReal.ofReal P.C_D ^ 3 * P.μ (ball z r)) := mul_le_mul_right hc _
    _ = _ := by ac_rfl

/-- At an uncapped stopping ball, the fivefold ball is eligible
for the maximal function at the stopping point. Its radius is at most κ. -/
theorem LocDoubling.stopping_ball_average (D : LocDoubling X) (f : X → ℝ)
    {z y : X} (hz : z ∈ D.Ω₁) {r α : ℝ} (hr : 0 < r) (hrκ : 5 * r ≤ D.κ)
    (hyz : dist y z < 4 * r)
    (hy : patchMaximal D.μ D.Ω₁ D.κ f y ≤ ENNReal.ofReal (D.C_D ^ 3 * α)) :
    (⨍⁻ x in ball z r, ‖f x‖ₑ ∂D.μ) ≤
      ENNReal.ofReal D.C_D ^ 3 * ENNReal.ofReal (D.C_D ^ 3 * α) := by
  have hlarge : (⨍⁻ x in ball z (5 * r), ‖f x‖ₑ ∂D.μ) ≤
      patchMaximal D.μ D.Ω₁ D.κ f y :=
    le_iSup_of_le z (le_iSup_of_le hz (le_iSup_of_le (5 * r)
      (le_iSup_of_le ⟨by positivity, hrκ⟩ (le_iSup_of_le (by linarith : dist y z < 5 * r) le_rfl))))
  exact (D.outerPatch.laverage_ball_le_five hz hr (by change r ≤ D.κ; linarith) f).trans
    (mul_le_mul_right (hlarge.trans hy) _)

/-- The capped Whitney ball is controlled by the uniform
κ-ball volume lower bound and the global input mass (BB p. 323). -/
theorem LocDoubling.capped_ball_average (D : LocDoubling X) (f : X → ℝ)
    (hf : IntegrableOn f D.Ω₂ D.μ) {z : X} (hz : z ∈ D.Ω₁)
    {m α : ℝ} (hm : 0 < m) (_hα : 0 ≤ α)
    (hml : ENNReal.ofReal m ≤ D.μ (ball z D.κ))
    (hmass : eLpNorm f 1 (D.μ.restrict D.Ω₂) ≤ ENNReal.ofReal α * D.μ D.Ω₁) :
    (⨍⁻ y in ball z (D.κ / 5), ‖f y‖ₑ ∂D.μ) ≤
      ENNReal.ofReal ((D.C_D ^ 3 * (D.μ D.Ω₁).toReal / m) * α) := by
  have hv := D.outerPatch.doubling z hz (D.κ / 5) (div_pos D.κ_pos (by norm_num))
    (by change D.κ / 5 ≤ 6 * D.κ; linarith [D.κ_pos])
  have hlower : ENNReal.ofReal m ≤ ENNReal.ofReal D.C_D ^ 3 *
      D.μ (ball z (D.κ / 5)) := hml.trans
    (D.outerPatch.compare_pow hz (div_pos D.κ_pos (by norm_num)) D.κ_pos
      (by change D.κ ≤ 6 * D.κ; linarith [D.κ_pos]) 3 (by norm_num; linarith [D.κ_pos]))
  have hone : (1 : ℝ≥0∞) ≤ (ENNReal.ofReal m)⁻¹ *
      (ENNReal.ofReal D.C_D ^ 3 * D.μ (ball z (D.κ / 5))) := by
    calc
      _ = (ENNReal.ofReal m)⁻¹ * ENNReal.ofReal m :=
        (ENNReal.inv_mul_cancel (by positivity) ENNReal.ofReal_ne_top).symm
      _ ≤ _ := mul_le_mul_right hlower _
  have hinside : ball z (D.κ / 5) ⊆ D.Ω₂ :=
    (ball_subset_ball (by change D.κ / 5 ≤ 6 * D.κ; linarith [D.κ_pos])).trans
      (D.outerPatch.incl z hz)
  have hI : (∫⁻ y in ball z (D.κ / 5), ‖f y‖ₑ ∂D.μ) ≤
      ENNReal.ofReal α * D.μ D.Ω₁ := by
    rw [eLpNorm_one_eq_lintegral_enorm hf.aestronglyMeasurable] at hmass
    exact (lintegral_mono' (Measure.restrict_mono hinside le_rfl) le_rfl).trans hmass
  have hV : D.μ D.Ω₁ ≠ ⊤ := ((measure_mono D.sub₁₂).trans_lt D.finΩ₂).ne
  have hC : 0 ≤ D.C_D ^ 3 := pow_nonneg (by linarith [D.one_lt_C_D]) _
  have he : ENNReal.ofReal ((D.C_D ^ 3 * (D.μ D.Ω₁).toReal / m) * α) =
      ENNReal.ofReal α * D.μ D.Ω₁ * (ENNReal.ofReal m)⁻¹ * ENNReal.ofReal D.C_D ^ 3 := by
    rw [ENNReal.ofReal_mul (div_nonneg (mul_nonneg hC ENNReal.toReal_nonneg) hm.le),
      ENNReal.ofReal_div_of_pos hm, ENNReal.ofReal_mul hC,
      ENNReal.ofReal_toReal hV, ENNReal.ofReal_pow (by linarith [D.one_lt_C_D]),
      div_eq_mul_inv]
    ac_rfl
  rw [setLAverage_eq, he]
  apply (ENNReal.div_le_iff hv.1.ne' hv.2.1.ne).mpr
  calc
    _ ≤ ENNReal.ofReal α * D.μ D.Ω₁ := hI
    _ ≤ (ENNReal.ofReal α * D.μ D.Ω₁) * ((ENNReal.ofReal m)⁻¹ *
        (ENNReal.ofReal D.C_D ^ 3 * D.μ (ball z (D.κ / 5)))) := by
      simpa only [mul_one] using mul_le_mul_right hone (ENNReal.ofReal α * D.μ D.Ω₁)
    _ = _ := by ac_rfl

end RothschildStein.H2

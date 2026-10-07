-- Copyright (c) 2026 Scott Armstrong and Amélie Loher. All rights reserved.
-- Released under Apache 2.0 license as described in the file LICENSE.
module
public import RothschildStein.H2.CampanatoLimit
public import RothschildStein.H2.UniformVolume
@[expose] public section
set_option autoImplicit false
set_option relaxedAutoImplicit false
noncomputable section
open Set MeasureTheory Metric
open scoped ENNReal
namespace RothschildStein.H2
variable {X : Type*} [MetricSpace X] [MeasurableSpace X] [BorelSpace X]

/-- The absolute value of a minimiser is bounded by oscillation plus
an average of |u| (BB Lemma 7.41, p. 329). -/
theorem campanatoConstant_abs (P : DoublingPatch X) {α : ℝ} {u : X → ℝ}
    (hu : MemCampanato α P u) {x : X} (hx : x ∈ P.S)
    {r : ℝ} (hr : 0 < r) (hrρ : r ≤ 6 * P.ρ) :
    |campanatoConstant P u x r| ≤ (campanatoSeminorm α P u).toReal * r ^ α +
      (∫ y in P.W, |u y| ∂P.μ) / (P.μ (ball x r)).toReal := by
  have hv := P.doubling x hx r hr hrρ
  let : IsFiniteMeasure (P.μ.restrict (ball x r)) := ⟨by simpa using hv.2.1⟩
  have hsub := (ball_subset_ball hrρ).trans (P.incl x hx)
  have hco := integralOscillation_coercive (hu.1.mono_set hsub)
    (campanatoConstant P u x r)
  simp only [Measure.restrict_apply_univ] at hco
  have hm : 0 < (P.μ (ball x r)).toReal := ENNReal.toReal_pos hv.1.ne' hv.2.1.ne
  have hb := campanatoConstant_integral_bound P hu hx hr hrρ
  have hI := setIntegral_mono_set hu.1.abs (ae_of_all _ fun _ => abs_nonneg _)
    (ae_of_all _ hsub)
  apply (mul_le_mul_iff_right₀ hm).mp
  have hdiv := div_mul_cancel₀ (∫ y in P.W, |u y| ∂P.μ) hm.ne'
  nlinarith

/-- Pointwise representative bound before replacing the ball volume
by the positive compact-centre infimum (BB Proposition 7.43, p. 330). -/
theorem campanatoRepresentative_abs (P : DoublingPatch X) {α : ℝ} (hα : 0 < α)
    {u : X → ℝ} (hu : MemCampanato α P u) {x : X} (hx : x ∈ P.S) :
    |campanatoRepresentative P α u x| ≤
      (1 + (P.C_D + 1) / (1 - (1 / 2 : ℝ) ^ α)) * (6 * P.ρ) ^ α *
        (campanatoSeminorm α P u).toReal +
      (∫ y in P.W, |u y| ∂P.μ) / (P.μ (ball x (6 * P.ρ))).toReal := by
  have hr : 0 < 6 * P.ρ := by linarith [P.ρ_pos]
  have ha := campanatoRepresentative_approx P hα hu hx hr le_rfl
  have hb := campanatoConstant_abs P hu hx hr le_rfl
  have ht := abs_sub_le (campanatoRepresentative P α u x)
    (campanatoConstant P u x (6 * P.ρ)) 0
  simp only [sub_zero] at ht
  rw [abs_sub_comm (campanatoRepresentative P α u x)] at ht
  nlinarith

/-- Uniform boundedness on compact-centre patches; the reciprocal
lower-volume term is retained as required by BB Remark 7.39. -/
theorem campanatoRepresentative_bounded (P : DoublingPatch X) {α : ℝ} (hα : 0 < α)
    {u : X → ℝ} (hu : MemCampanato α P u) :
    ∃ B : ℝ, ∀ x ∈ P.S, |campanatoRepresentative P α u x| ≤ B := by
  obtain ⟨m, hm, hb⟩ := P.exists_uniform_lower (show 0 < 6 * P.ρ by linarith [P.ρ_pos]) le_rfl
  let m' := min m 1
  have hmp : 0 < m' := lt_min hm (by norm_num)
  have hmt : m' < ⊤ := (min_le_right _ _).trans_lt (by norm_num)
  have hmr : 0 < m'.toReal := ENNReal.toReal_pos hmp.ne' hmt.ne
  refine ⟨(1 + (P.C_D + 1) / (1 - (1 / 2 : ℝ) ^ α)) * (6 * P.ρ) ^ α *
    (campanatoSeminorm α P u).toReal + (∫ y in P.W, |u y| ∂P.μ) / m'.toReal, ?_⟩
  intro x hx
  apply (campanatoRepresentative_abs P hα hu hx).trans
  apply add_le_add le_rfl
  have hv := P.doubling x hx (6 * P.ρ) (by linarith [P.ρ_pos]) le_rfl
  have hvb := ENNReal.toReal_mono hv.2.1.ne ((min_le_left m (1 : ℝ≥0∞)).trans (hb x hx))
  exact div_le_div_of_nonneg_left (integral_nonneg fun _ => abs_nonneg _) hmr hvb
end RothschildStein.H2

-- Copyright (c) 2026 Scott Armstrong and Amélie Loher. All rights reserved.
-- Released under Apache 2.0 license as described in the file LICENSE.
module
public import RothschildStein.H2.CampanatoMinimizer
public import RothschildStein.H2.HolderSpaces
public import Mathlib.MeasureTheory.Integral.Bochner.Set
@[expose] public section
set_option autoImplicit false
set_option relaxedAutoImplicit false
noncomputable section
open Set MeasureTheory Metric
open scoped ENNReal
namespace RothschildStein.H2
variable {X : Type*} [MetricSpace X] [MeasurableSpace X] [BorelSpace X]

/-- Local Campanato seminorm, a number rather than a function.
BB Definition 7.37, p. 327; centers lie in the patch S. -/
def campanatoSeminorm (α : ℝ) (P : DoublingPatch X) (u : X → ℝ) : ℝ≥0∞ :=
  ⨆ (x ∈ P.S) (r ∈ Ioc 0 (6 * P.ρ)),
    ⨅ c : ℝ, ENNReal.ofReal
      (integralOscillation (P.μ.restrict (ball x r)) u c /
        (r ^ α * (P.μ (ball x r)).toReal))

/-- Membership includes the outer L¹ condition of BB Definition 7.37. -/
def MemCampanato (α : ℝ) (P : DoublingPatch X) (u : X → ℝ) : Prop :=
  IntegrableOn u P.W P.μ ∧ campanatoSeminorm α P u < ⊤

/-- Every controlled ball has a minimising constant. -/
theorem DoublingPatch.exists_oscillation_minimizer (P : DoublingPatch X)
    {u : X → ℝ} (hu : IntegrableOn u P.W P.μ) {x : X} (hx : x ∈ P.S)
    {r : ℝ} (hr : 0 < r) (hrρ : r ≤ 6 * P.ρ) :
    ∃ c : ℝ, ∀ d : ℝ,
      integralOscillation (P.μ.restrict (ball x r)) u c ≤
        integralOscillation (P.μ.restrict (ball x r)) u d := by
  have hv := P.doubling x hx r hr hrρ
  let : IsFiniteMeasure (P.μ.restrict (ball x r)) := ⟨by simpa using hv.2.1⟩
  apply exists_integralOscillation_minimizer (by simpa using hv.1)
  exact hu.mono_set ((ball_subset_ball hrρ).trans (P.incl x hx))

/-- A minimiser realizes the Campanato integral bound. -/
theorem DoublingPatch.oscillation_minimizer_bound (P : DoublingPatch X)
    {α : ℝ} {u : X → ℝ} (hu : MemCampanato α P u)
    {x : X} (hx : x ∈ P.S) {r : ℝ} (hr : 0 < r) (hrρ : r ≤ 6 * P.ρ)
    {c : ℝ} (hc : ∀ d : ℝ,
      integralOscillation (P.μ.restrict (ball x r)) u c ≤
        integralOscillation (P.μ.restrict (ball x r)) u d) :
    integralOscillation (P.μ.restrict (ball x r)) u c ≤
      (campanatoSeminorm α P u).toReal * r ^ α * (P.μ (ball x r)).toReal := by
  have hv := P.doubling x hx r hr hrρ
  have hm : 0 < (P.μ (ball x r)).toReal := ENNReal.toReal_pos hv.1.ne' hv.2.1.ne
  have hp : 0 < r ^ α * (P.μ (ball x r)).toReal := mul_pos (Real.rpow_pos_of_pos hr _) hm
  have hmin : ENNReal.ofReal
      (integralOscillation (P.μ.restrict (ball x r)) u c /
        (r ^ α * (P.μ (ball x r)).toReal)) ≤ campanatoSeminorm α P u := by
    apply le_trans (le_iInf fun d => ENNReal.ofReal_le_ofReal
      (div_le_div_of_nonneg_right (hc d) hp.le))
    exact le_iSup_of_le x (le_iSup_of_le hx (le_iSup_of_le r
      (le_iSup_of_le ⟨hr, hrρ⟩ le_rfl)))
  have hn : 0 ≤ integralOscillation (P.μ.restrict (ball x r)) u c :=
    integral_nonneg fun _ => abs_nonneg _
  have ht := ENNReal.toReal_mono hu.2.ne hmin
  rw [ENNReal.toReal_ofReal (div_nonneg hn hp.le)] at ht
  have ht' := (div_le_iff₀ hp).mp ht
  nlinarith
end RothschildStein.H2

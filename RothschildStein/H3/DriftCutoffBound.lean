-- Copyright (c) 2026 Scott Armstrong and Amélie Loher. All rights reserved.
-- Released under Apache 2.0 license as described in the file LICENSE.
module

public import RothschildStein.H3.SecondGaugeBounds
public import RothschildStein.H3.PlateauWords

set_option autoImplicit false
set_option relaxedAutoImplicit false
@[expose] public section
noncomputable section
namespace RothschildStein.H3
variable {N q : ℕ} (G : HomogeneousGroup N)

/-- The drift cutoff bound has inverse-gap order two, uniformly in
center and radii. The inner-radius assumption is exactly t >= s/2. -/
theorem exists_drift_cutoff_bound (H : H1.StandingHypotheses G q)
    (ν : G2.HomogeneousNorm G) (hν : ν.Smooth) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ x₀ : Fin N → ℝ, ∀ t s : ℝ,
      0 < t → t < s → s / 2 ≤ t → ∀ x : Fin N → ℝ,
      |fieldDerivative (H.fields 0) (smoothQuasiballCutoff G ν x₀ t s) x| ≤
        C / (s - t)^2 := by
  obtain ⟨M, hM, hb⟩ := gauge_driftDerivative_bound G H ν hν
  obtain ⟨κ, hκ, hk⟩ := exists_quasiballProfile_derivative_bound (by norm_num : 0 < (1 : ℕ))
  have hrad : ∀ t s : ℝ, 0 < t → t < s → s / 2 ≤ t → ∀ x : Fin N → ℝ,
      |fieldDerivative (H.fields 0) (quasiballProfile t s ∘ ν) x| ≤
        (2 * κ * M) / (s - t)^2 := by
    intro t s ht hts hhalf x
    by_cases hx : ν x < t
    · have he := radialProfile_wordDerivative_zero_below G ν H.fields [0]
        (by simp) hts hx
      simp only [wordDerivative] at he
      rw [he, abs_zero]
      positivity
    · have htx : t ≤ ν x := le_of_not_gt hx
      have hx0 : x ≠ 0 := by
        intro he
        rw [he, (ν.gauge.2.2.1 0).mpr rfl] at htx
        exact (not_le.mpr ht) htx
      have hg : 0 < s - t := sub_pos.mpr hts
      have hgap : s - t ≤ ν x := by linarith
      have hb' : |fieldDerivative (H.fields 0) ν x| ≤ M / (s - t) :=
        (hb x hx0).trans (div_le_div_of_nonneg_left hM hg hgap)
      rw [fieldDerivative_quasiballProfile G ν hν _ t s hx0, abs_mul]
      have hk' : |deriv (quasiballProfile t s) (ν x)| ≤ κ * (2 / (s - t)) := by
        simpa only [iteratedDeriv_one, pow_one] using hk t s hts (ν x)
      have hprod := mul_le_mul hk' hb' (abs_nonneg _) (by positivity)
      exact hprod.trans_eq (by field_simp [hg.ne'])
  refine ⟨2 * κ * M, by positivity, ?_⟩
  intro x₀ t s ht hts hhalf x
  have he := congrFun (wordDerivative_smoothQuasiballCutoff G ν hν H.fields
    (H.fields_smooth G) H.invariant [0] x₀ ht hts) x
  simp only [wordDerivative, Function.comp_apply] at he
  rw [he]
  exact hrad t s ht hts hhalf _

end RothschildStein.H3

-- Copyright (c) 2026 Scott Armstrong and Amélie Loher. All rights reserved.
-- Released under Apache 2.0 license as described in the file LICENSE.
module

public import RothschildStein.H3.SecondGaugeBounds
public import RothschildStein.H3.SecondRadialChain
public import RothschildStein.H3.PlateauWords

set_option autoImplicit false
set_option relaxedAutoImplicit false
@[expose] public section
noncomputable section
namespace RothschildStein.H3
variable {N q : ℕ} (G : HomogeneousGroup N)

/-- Ordered second horizontal cutoff derivatives have uniform
inverse-square gap bounds at every center, with the exact inner-radius range. -/
theorem exists_secondHorizontal_cutoff_bound (H : H1.StandingHypotheses G q)
    (ν : G2.HomogeneousNorm G) (hν : ν.Smooth) (i j : Fin q) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ x₀ : Fin N → ℝ, ∀ t s : ℝ,
      0 < t → t < s → s / 2 ≤ t → ∀ x : Fin N → ℝ,
      |fieldDerivative (H.fields i.succ)
        (fieldDerivative (H.fields j.succ) (smoothQuasiballCutoff G ν x₀ t s)) x| ≤
        C / (s - t)^2 := by
  obtain ⟨Mi, hMi, hbi⟩ := gauge_horizontalDerivative_bound G H ν hν i
  obtain ⟨Mj, hMj, hbj⟩ := gauge_horizontalDerivative_bound G H ν hν j
  obtain ⟨Mij, hMij, hbij⟩ := gauge_secondHorizontalDerivative_bound G H ν hν i j
  obtain ⟨κ₁, hκ₁, hk₁⟩ := exists_quasiballProfile_derivative_bound (by norm_num : 0 < (1 : ℕ))
  obtain ⟨κ₂, hκ₂, hk₂⟩ := exists_quasiballProfile_derivative_bound (by norm_num : 0 < (2 : ℕ))
  let C := 4 * κ₂ * Mi * Mj + 2 * κ₁ * Mij
  have hC : 0 ≤ C := by dsimp [C]; positivity
  have hrad : ∀ t s : ℝ, 0 < t → t < s → s / 2 ≤ t → ∀ x : Fin N → ℝ,
      |fieldDerivative (H.fields i.succ)
        (fieldDerivative (H.fields j.succ) (quasiballProfile t s ∘ ν)) x| ≤
        C / (s - t)^2 := by
    intro t s ht hts hhalf x
    by_cases hx : ν x < t
    · have he := radialProfile_wordDerivative_zero_below G ν H.fields [i.succ, j.succ]
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
      have hbij' : |fieldDerivative (H.fields i.succ) (fieldDerivative (H.fields j.succ) ν) x|
          ≤ Mij / (s - t) :=
        (hbij x hx0).trans (div_le_div_of_nonneg_left hMij hg hgap)
      have hk₁' : |deriv (quasiballProfile t s) (ν x)| ≤ κ₁ * (2 / (s - t)) := by
        simpa only [iteratedDeriv_one, pow_one] using hk₁ t s hts (ν x)
      have hk₂' : |deriv (deriv (quasiballProfile t s)) (ν x)| ≤ κ₂ * (2 / (s - t))^2 := by
        simpa only [show (2 : ℕ) = 1 + 1 by rfl, iteratedDeriv_succ, iteratedDeriv_one, iteratedDeriv_zero] using
          hk₂ t s hts (ν x)
      rw [fieldDerivative_second_scalar_comp _ _ (quasiballProfile_contDiff t s)
        hν (H.fields_smooth G j.succ) hx0]
      have hA := mul_le_mul (mul_le_mul hk₂' (hbi x hx0) (abs_nonneg _) (by positivity))
        (hbj x hx0) (abs_nonneg _) (by positivity)
      have hB := mul_le_mul hk₁' hbij' (abs_nonneg _) (by positivity)
      calc
        _ ≤ |deriv (deriv (quasiballProfile t s)) (ν x) *
              fieldDerivative (H.fields i.succ) ν x * fieldDerivative (H.fields j.succ) ν x| +
            |deriv (quasiballProfile t s) (ν x) *
              fieldDerivative (H.fields i.succ) (fieldDerivative (H.fields j.succ) ν) x| := abs_add_le _ _
        _ ≤ (κ₂ * (2 / (s - t))^2 * Mi) * Mj +
            (κ₁ * (2 / (s - t))) * (Mij / (s - t)) := by
          simpa only [abs_mul] using add_le_add hA hB
        _ = C / (s - t)^2 := by dsimp [C]; field_simp [hg.ne']; ring
  refine ⟨C, hC, ?_⟩
  intro x₀ t s ht hts hhalf x
  have he := congrFun (wordDerivative_smoothQuasiballCutoff G ν hν H.fields
    (H.fields_smooth G) H.invariant [i.succ, j.succ] x₀ ht hts) x
  simp only [wordDerivative, Function.comp_apply] at he
  rw [he]
  exact hrad t s ht hts hhalf _

end RothschildStein.H3

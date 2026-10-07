-- Copyright (c) 2026 Scott Armstrong and Amélie Loher. All rights reserved.
-- Released under Apache 2.0 license as described in the file LICENSE.
module

public import RothschildStein.H1.PrincipalValueErrorIdentity

set_option autoImplicit false
set_option relaxedAutoImplicit false
@[expose] public section
noncomputable section
open Set MeasureTheory Filter
namespace RothschildStein.H1
variable {N : ℕ} (G : HomogeneousGroup N)

/-- The principal-value truncation error is uniformly
bounded by Cε, with C independent of the base point. -/
theorem exists_principalValue_uniform_error_bound
    {ν F ψ : (Fin N → ℝ) → ℝ} (hν : G.IsHomogeneousGauge ν)
    (hF : ContinuousOn F {(0 : Fin N → ℝ)}ᶜ)
    (hhom : ∀ t : ℝ, 0 < t → ∀ x, x ≠ 0 →
      F (G.dilate t x) = t ^ (-(G.homogeneousDimension : ℝ)) * F x)
    (hcancel : HasVanishingShellIntegrals ν F)
    (hc : ContDiff ℝ 1 ψ) (hs : HasCompactSupport ψ) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ ε : ℝ, 0 < ε → ε < 1 → ∀ x,
      ‖principalValueTruncation G ν F ψ ε x - principalValueConvolution G ν F ψ x‖ ≤ C * ε := by
  obtain ⟨C, hC, hb⟩ := exists_principalValue_near_bound G hν hF hhom hc hs
  refine ⟨C * ((G.homogeneousDimension : ℝ) * (volume {w | ν w < 1}).toReal),
    mul_nonneg hC (mul_nonneg (Nat.cast_nonneg _) ENNReal.toReal_nonneg), ?_⟩
  intro ε hε hε1 x
  have hp : IntegrableOn (fun w => (ν w) ^ (1 - (G.homogeneousDimension : ℝ)))
      {w | ν w ≤ ε} volume := by
    have he : -((G.homogeneousDimension : ℝ) - 1) = 1 - (G.homogeneousDimension : ℝ) := by ring
    simpa only [he] using (G2.integrableOn_power_near_iff hν
      ((G.homogeneousDimension : ℝ) - 1) hε).mpr (by linarith)
  have heq : (∫ w in {w | ν w ≤ ε}, (ν w) ^ (1 - (G.homogeneousDimension : ℝ))) =
      (G.homogeneousDimension : ℝ) * (volume {w | ν w < 1}).toReal * ε := by
    have he : -((G.homogeneousDimension : ℝ) - 1) = 1 - (G.homogeneousDimension : ℝ) := by ring
    have hd : (G.homogeneousDimension : ℝ) - ((G.homogeneousDimension : ℝ) - 1) = 1 := by ring
    simpa only [he, hd, Real.rpow_one, div_one] using
      G2.integral_power_near hν (β := (G.homogeneousDimension : ℝ) - 1) (by linarith) hε
  rw [principalValueTruncation_sub_eq_neg_smallIntegral G hν hF hhom hcancel hc hs hε hε1, norm_neg]
  calc
    _ ≤ ∫ w in {w | ν w ≤ ε}, C * (ν w) ^ (1 - (G.homogeneousDimension : ℝ)) := by
      apply norm_integral_le_of_norm_le (hp.const_mul C)
      filter_upwards [ae_restrict_mem (isClosed_le hν.1 continuous_const).measurableSet] with w hw
      exact hb x w (hw.trans hε1.le)
    _ = _ := by rw [integral_const_mul, heq]; ring

end RothschildStein.H1

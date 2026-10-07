-- Copyright (c) 2026 Scott Armstrong and Amélie Loher. All rights reserved.
-- Released under Apache 2.0 license as described in the file LICENSE.
module

public import RothschildStein.H1.PrincipalValueNearIntegrability

set_option autoImplicit false
set_option relaxedAutoImplicit false
@[expose] public section
noncomputable section
open Set MeasureTheory Filter
namespace RothschildStein.H1
variable {N : ℕ} (G : HomogeneousGroup N)

/-- Step 4: bounded cutoff weights retain the uniform
Cρ error bound for the subtracted critical kernel in a small ball. -/
theorem exists_criticalKernel_weightedSmallBall_bound
    {ν F ψ : (Fin N → ℝ) → ℝ} (hν : G.IsHomogeneousGauge ν)
    (hF : ContinuousOn F {(0 : Fin N → ℝ)}ᶜ)
    (hhom : ∀ t : ℝ, 0 < t → ∀ x, x ≠ 0 →
      F (G.dilate t x) = t ^ (-(G.homogeneousDimension : ℝ)) * F x)
    (hc : ContDiff ℝ 1 ψ) (hs : HasCompactSupport ψ) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ ρ : ℝ, 0 < ρ → ρ ≤ 1 →
      ∀ η : (Fin N → ℝ) → ℝ, (∀ w, ‖η w‖ ≤ 1) → ∀ x,
      ‖∫ w in {w | ν w ≤ ρ}, η w * (F w * (ψ (G.mul x (G.inv w)) - ψ x))‖ ≤ C * ρ := by
  obtain ⟨C, hC, hb⟩ := exists_principalValue_near_bound G hν hF hhom hc hs
  refine ⟨C * ((G.homogeneousDimension : ℝ) * (volume {w | ν w < 1}).toReal),
    mul_nonneg hC (mul_nonneg (Nat.cast_nonneg _) ENNReal.toReal_nonneg), ?_⟩
  intro ρ hρ hρ1 η hη x
  have hp : IntegrableOn (fun w => (ν w) ^ (1 - (G.homogeneousDimension : ℝ))) {w | ν w ≤ ρ} volume := by
    have he : -((G.homogeneousDimension : ℝ) - 1) = 1 - (G.homogeneousDimension : ℝ) := by ring
    simpa only [he] using (G2.integrableOn_power_near_iff hν ((G.homogeneousDimension : ℝ) - 1) hρ).mpr (by linarith)
  have heq : (∫ w in {w | ν w ≤ ρ}, (ν w) ^ (1 - (G.homogeneousDimension : ℝ))) =
      (G.homogeneousDimension : ℝ) * (volume {w | ν w < 1}).toReal * ρ := by
    have he : -((G.homogeneousDimension : ℝ) - 1) = 1 - (G.homogeneousDimension : ℝ) := by ring
    have hd : (G.homogeneousDimension : ℝ) - ((G.homogeneousDimension : ℝ) - 1) = 1 := by ring
    simpa only [he, hd, Real.rpow_one, div_one] using
      G2.integral_power_near hν (β := (G.homogeneousDimension : ℝ) - 1) (by linarith) hρ
  calc
    _ ≤ ∫ w in {w | ν w ≤ ρ}, C * (ν w) ^ (1 - (G.homogeneousDimension : ℝ)) := by
      apply norm_integral_le_of_norm_le (hp.const_mul C)
      filter_upwards [ae_restrict_mem (isClosed_le hν.1 continuous_const).measurableSet] with w hw
      rw [norm_mul]
      exact (mul_le_mul (hη w) (hb x w (hw.trans hρ1)) (norm_nonneg _) zero_le_one).trans_eq (one_mul _)
    _ = _ := by rw [integral_const_mul, heq]; ring

end RothschildStein.H1

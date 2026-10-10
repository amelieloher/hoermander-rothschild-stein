-- Copyright (c) 2026 Scott Armstrong and Amélie Loher. All rights reserved.
-- Released under Apache 2.0 license as described in the file LICENSE.
module

public import HeatKernel.Moser.NonlinearEnergyDifferentiability

/-! # Local Lipschitz bounds for nonlinear integral energies

The weighted first variation has norm bounded by the L² norm of the base function.
The mean value theorem gives a uniform Lipschitz bound on each bounded L² ball.
-/

@[expose] public section

open MeasureTheory Filter Set
open scoped NNReal

namespace HeatKernel

/-- The derivative norm of the nonlinear energy is bounded by the base L² norm. -/
theorem norm_fderiv_weighted_nonlinear_energy_le {α : Type*} [MeasurableSpace α]
    {μ : Measure α} {Φ : ℝ → ℝ} {L : ℝ≥0}
    (hΦ : Differentiable ℝ Φ) (hL : LipschitzWith L (deriv Φ))
    (hzero : Φ 0 = 0) (hdzero : deriv Φ 0 = 0)
    {ψ : α → ℝ} (hψ : AEStronglyMeasurable ψ μ)
    {A : ℝ≥0} (hb : ∀ᵐ x ∂μ, ‖ψ x‖ ≤ A) (v : Lp ℝ 2 μ) :
    ‖fderiv ℝ (fun w : Lp ℝ 2 μ => ∫ x, ψ x * Φ (w x) ∂μ) v‖ ≤
      ((A * L : ℝ≥0) : ℝ) * ‖v‖ := by
  obtain ⟨g, hg, hd⟩ := exists_hasFDerivAt_weighted_nonlinear_energy
    hΦ hL hzero hdzero hψ A.coe_nonneg hb v
  rw [hd.fderiv, innerSL_apply_norm]
  apply Lp.norm_le_mul_norm_of_ae_le_mul
  filter_upwards [hg, hb] with x hx hψx
  rw [hx, norm_mul]
  have hD : ‖deriv Φ (v x)‖ ≤ (L : ℝ) * ‖v x‖ := by
    simpa only [hdzero, sub_zero] using hL.norm_sub_le (v x) 0
  exact (mul_le_mul hψx hD (norm_nonneg _) A.coe_nonneg).trans_eq (by simp [mul_assoc])

/-- On each closed L² ball the weighted nonlinear energy is Lipschitz. -/
theorem lipschitzOnWith_weighted_nonlinear_energy_closedBall {α : Type*} [MeasurableSpace α]
    {μ : Measure α} {Φ : ℝ → ℝ} {L : ℝ≥0}
    (hΦ : Differentiable ℝ Φ) (hL : LipschitzWith L (deriv Φ))
    (hzero : Φ 0 = 0) (hdzero : deriv Φ 0 = 0)
    {ψ : α → ℝ} (hψ : AEStronglyMeasurable ψ μ)
    {A : ℝ≥0} (hb : ∀ᵐ x ∂μ, ‖ψ x‖ ≤ A) (R : ℝ≥0) :
    LipschitzOnWith (A * L * R) (fun w : Lp ℝ 2 μ => ∫ x, ψ x * Φ (w x) ∂μ)
      (Metric.closedBall 0 (R : ℝ)) := by
  apply Convex.lipschitzOnWith_of_nnnorm_fderiv_le (𝕜 := ℝ)
  · intro v _
    obtain ⟨_, _, hd⟩ := exists_hasFDerivAt_weighted_nonlinear_energy
      hΦ hL hzero hdzero hψ A.coe_nonneg hb v
    exact hd.differentiableAt
  · intro v hv
    have hvR : ‖v‖ ≤ (R : ℝ) := by simpa only [Metric.mem_closedBall, dist_zero_right] using hv
    have H := (norm_fderiv_weighted_nonlinear_energy_le hΦ hL hzero hdzero hψ hb v).trans
      (mul_le_mul_of_nonneg_left hvR (NNReal.coe_nonneg (A * L)))
    exact_mod_cast H
  · exact convex_closedBall (0 : Lp ℝ 2 μ) (R : ℝ)

end HeatKernel

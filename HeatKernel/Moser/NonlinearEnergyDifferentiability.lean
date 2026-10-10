-- Copyright (c) 2026 Scott Armstrong and Amélie Loher. All rights reserved.
-- Released under Apache 2.0 license as described in the file LICENSE.
module

public import HeatKernel.Moser.NonlinearEnergyVariation

/-! # Fréchet differentiability of weighted nonlinear energies on L²

For a nonlinearity vanishing to first order at zero with Lipschitz derivative, its weighted
integral energy is Fréchet differentiable. The derivative is the spatial first variation.
-/

@[expose] public section

open MeasureTheory Filter
open scoped NNReal

namespace HeatKernel

/-- The weighted integral energy is Fréchet differentiable on L² when the scalar derivative
is Lipschitz and the nonlinearity vanishes to first order at zero. -/
theorem exists_hasFDerivAt_weighted_nonlinear_energy {α : Type*} [MeasurableSpace α]
    {μ : Measure α} {Φ : ℝ → ℝ} {L : ℝ≥0}
    (hΦ : Differentiable ℝ Φ) (hL : LipschitzWith L (deriv Φ))
    (hzero : Φ 0 = 0) (hdzero : deriv Φ 0 = 0)
    {ψ : α → ℝ} (hψ : AEStronglyMeasurable ψ μ)
    {A : ℝ} (hA : 0 ≤ A) (hb : ∀ᵐ x ∂μ, ‖ψ x‖ ≤ A) (v : Lp ℝ 2 μ) :
    ∃ g : Lp ℝ 2 μ, g =ᵐ[μ] (fun x => ψ x * deriv Φ (v x)) ∧
      HasFDerivAt (fun w : Lp ℝ 2 μ => ∫ x, ψ x * Φ (w x) ∂μ) (innerSL ℝ g) v := by
  obtain ⟨g, hg, haction⟩ := exists_weighted_nonlinear_energy_variation hL hdzero hψ hA hb v
  refine ⟨g, hg, hasFDerivAt_of_quadratic_remainder (innerSL ℝ g) (C := A * L) ?_⟩
  intro k
  have hi0 := integrable_weighted_nonlinearity_of_lipschitz_deriv hΦ hL hzero hdzero hψ hA hb v
  have hi1 := integrable_weighted_nonlinearity_of_lipschitz_deriv hΦ hL hzero hdzero hψ hA hb (v + k)
  have hadd : (fun x => ψ x * Φ ((v + k) x)) =ᵐ[μ]
      (fun x => ψ x * Φ (v x + k x)) := by
    filter_upwards [Lp.coeFn_add v k] with x hx
    simp only [Pi.add_apply] at hx
    rw [hx]
  have hi1' := (integrable_congr hadd).mp hi1
  have hlin : Integrable (fun x => ψ x * deriv Φ (v x) * k x) μ := by
    have he : (fun x => g x * k x) =ᵐ[μ] (fun x => ψ x * deriv Φ (v x) * k x) := by
      filter_upwards [hg] with x hx
      rw [hx]
    exact (integrable_congr he).mp ((Lp.memLp g).integrable_mul (Lp.memLp k))
  have he : (∫ x, ψ x * Φ ((v + k) x) ∂μ) - (∫ x, ψ x * Φ (v x) ∂μ) -
      (innerSL ℝ g) k =
      ∫ x, ψ x * (Φ (v x + k x) - Φ (v x) - deriv Φ (v x) * k x) ∂μ := by
    rw [haction k, integral_congr_ae hadd]
    rw [← integral_sub hi1' hi0]
    have hsub := integral_sub (hi1'.sub hi0) hlin
    simp only [Pi.sub_def] at hsub
    rw [← hsub]
    apply integral_congr_ae
    exact Eventually.of_forall fun x => by ring
  rw [he]
  exact (integrable_and_norm_integral_weighted_taylor_remainder hΦ hL
    (Lp.aestronglyMeasurable v) hψ hA hb k).2

end HeatKernel

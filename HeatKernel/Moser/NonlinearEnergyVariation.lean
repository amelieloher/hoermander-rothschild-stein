-- Copyright (c) 2026 Scott Armstrong and Amélie Loher. All rights reserved.
-- Released under Apache 2.0 license as described in the file LICENSE.
module

public import HeatKernel.Moser.NonlinearEnergyIntegrability

/-! # Continuous linear variations of weighted nonlinear energies

The square integrable weighted derivative represents a bounded linear functional by the
Hilbert inner product. Its action agrees with the spatial first-variation integral.
-/

@[expose] public section

open MeasureTheory Filter
open scoped NNReal

namespace HeatKernel

/-- The weighted scalar derivative has an L² representative whose inner-product functional
agrees with the first-variation integral for every L² increment. -/
theorem exists_weighted_nonlinear_energy_variation {α : Type*} [MeasurableSpace α]
    {μ : Measure α} {Φ : ℝ → ℝ} {L : ℝ≥0}
    (hL : LipschitzWith L (deriv Φ)) (hdzero : deriv Φ 0 = 0)
    {ψ : α → ℝ} (hψ : AEStronglyMeasurable ψ μ)
    {A : ℝ} (hA : 0 ≤ A) (hb : ∀ᵐ x ∂μ, ‖ψ x‖ ≤ A) (v : Lp ℝ 2 μ) :
    ∃ g : Lp ℝ 2 μ, g =ᵐ[μ] (fun x => ψ x * deriv Φ (v x)) ∧
      ∀ k : Lp ℝ 2 μ, (innerSL ℝ g) k = ∫ x, ψ x * deriv Φ (v x) * k x ∂μ := by
  have hg := memLp_weighted_deriv_of_lipschitz_deriv hL hdzero hψ hA hb v
  let g := hg.toLp (fun x => ψ x * deriv Φ (v x))
  have he : g =ᵐ[μ] (fun x => ψ x * deriv Φ (v x)) := hg.coeFn_toLp
  refine ⟨g, he, fun k => ?_⟩
  rw [innerSL_apply_apply, L2.inner_def]
  apply integral_congr_ae
  filter_upwards [he] with x hx
  simp [hx, mul_comm]

end HeatKernel

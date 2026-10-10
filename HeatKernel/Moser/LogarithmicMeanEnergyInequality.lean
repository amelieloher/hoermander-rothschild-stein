-- Copyright (c) 2026 Scott Armstrong and Amélie Loher. All rights reserved.
-- Released under Apache 2.0 license as described in the file LICENSE.
module

public import HeatKernel.Moser.LogarithmicCutoffEnergyBound
import Mathlib.Tactic
import all Mathlib.Basic.Real.Basic

/-! # Normalized logarithmic mean differential inequalities -/

@[expose] public section
set_option autoImplicit false
set_option relaxedAutoImplicit false
noncomputable section
open MeasureTheory
namespace HeatKernel

/-- A mean whose derivative is the normalized reciprocal flux retains half the
normalized logarithmic energy, with the exact normalized cutoff error. The spatial
square-integrability inputs supply the integrability needed for absorption. -/
theorem shifted_logarithmic_mean_deriv_lower_bound {α ι : Type*}
    [MeasurableSpace α] [Fintype ι] {μ : Measure α}
    {a : ι → ι → α → ℝ} {u η : α → ℝ} {g d : ι → α → ℝ}
    {c C K mass t : ℝ} {m : ℝ → ℝ}
    (hc : 0 < c) (hmass : 0 < mass)
    (hu : AEStronglyMeasurable u μ) (hupos : ∀ᵐ x ∂μ, 0 ≤ u x)
    (hη : AEStronglyMeasurable η μ) (hηbound : ∀ᵐ x ∂μ, ‖η x‖ ≤ K)
    (ha : ∀ i j, AEStronglyMeasurable (a i j) μ)
    (hb : ∀ i j, ∀ᵐ x ∂μ, ‖a i j x‖ ≤ C)
    (hg : ∀ i, MemLp (g i) 2 μ) (hd : ∀ i, MemLp (d i) 2 μ)
    (hsym : ∀ᵐ x ∂μ, ∀ i j, a i j x = a j i x)
    (hpos : ∀ᵐ x ∂μ, ∀ ξ, 0 ≤ matrixEnergy (fun i j => a i j x) ξ)
    (hder : HasDerivAt m (mass⁻¹ * (-(∑ i, ∫ x, (∑ j, a i j x * g j x) *
      (η x ^ 2 * (-((u x + c) ^ 2)⁻¹ * g i x) +
        (2 * η x * d i x) * (u x + c)⁻¹) ∂μ))) t) :
    let v := fun i x => η x * ((u x + c)⁻¹ * g i x)
    mass⁻¹ * (∫ x, ∑ i, ∑ j, a i j x * v j x * v i x ∂μ) / 2 -
      2 * mass⁻¹ * (∫ x, ∑ i, ∑ j, a i j x * d j x * d i x ∂μ) ≤ deriv m t := by
  have h := mul_le_mul_of_nonneg_left
    (integral_shifted_logarithmic_flux_absorption hc hu hupos hη hηbound ha hb hg hd hsym hpos)
    (inv_nonneg.mpr hmass.le)
  rw [sum_integral_shifted_logarithmic_flux_eq hc hu hupos hη hηbound ha hb hg hd] at hder
  rw [hder.deriv]
  dsimp only at h ⊢
  nlinarith

end HeatKernel

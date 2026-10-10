-- Copyright (c) 2026 Scott Armstrong and Amélie Loher. All rights reserved.
-- Released under Apache 2.0 license as described in the file LICENSE.
module

public import HeatKernel.Moser.JointMeasurability
import Mathlib.Tactic
import all Mathlib.Basic.Real.Basic

/-! # Integrability of positively shifted logarithmic flux densities -/

@[expose] public section
set_option autoImplicit false
set_option relaxedAutoImplicit false
noncomputable section
open MeasureTheory
namespace HeatKernel

/-- A positive shift makes the reciprocal multiplier bounded on nonnegative values,
so each logarithmic gradient component remains square integrable. -/
theorem memLp_shifted_logarithmic_gradient {α : Type*} [MeasurableSpace α]
    {μ : Measure α} {u g : α → ℝ} {c : ℝ} (hc : 0 < c)
    (hu : AEStronglyMeasurable u μ) (hupos : ∀ᵐ x ∂μ, 0 ≤ u x)
    (hg : MemLp g 2 μ) : MemLp (fun x => (u x + c)⁻¹ * g x) 2 μ := by
  apply memLp_two_mul_of_ae_bound (C := c⁻¹)
    ((hu.add aestronglyMeasurable_const).inv₀) hg
  filter_upwards [hupos] with x hx
  have hp : 0 < u x + c := add_pos_of_nonneg_of_pos hx hc
  change ‖(u x + c)⁻¹‖ ≤ c⁻¹
  rw [Real.norm_eq_abs, abs_of_pos (inv_pos.mpr hp)]
  simpa only [one_div] using one_div_le_one_div_of_le hc (le_add_of_nonneg_left hx)

/-- Bounded measurable matrix coefficients pair any two square-integrable vector
families into an integrable density. -/
theorem integrable_matrix_pairing {α ι : Type*} [MeasurableSpace α] [Fintype ι]
    {μ : Measure α} {a : ι → ι → α → ℝ} {v w : ι → α → ℝ} {C : ℝ}
    (ha : ∀ i j, AEStronglyMeasurable (a i j) μ)
    (hb : ∀ i j, ∀ᵐ x ∂μ, ‖a i j x‖ ≤ C)
    (hv : ∀ i, MemLp (v i) 2 μ) (hw : ∀ i, MemLp (w i) 2 μ) :
    Integrable (fun x => ∑ i, ∑ j, a i j x * v j x * w i x) μ := by
  apply integrable_finsetSum
  intro i _
  apply integrable_finsetSum
  intro j _
  exact (memLp_two_mul_of_ae_bound (ha i j) (hv j) (hb i j)).integrable_mul (hw i)

/-- The principal, mixed and cutoff densities are separately integrable for a
bounded cutoff and square-integrable original and cutoff gradients. -/
theorem integrable_shifted_logarithmic_flux_terms {α ι : Type*}
    [MeasurableSpace α] [Fintype ι] {μ : Measure α}
    {a : ι → ι → α → ℝ} {u η : α → ℝ} {g d : ι → α → ℝ} {c C K : ℝ}
    (hc : 0 < c) (hu : AEStronglyMeasurable u μ) (hupos : ∀ᵐ x ∂μ, 0 ≤ u x)
    (hη : AEStronglyMeasurable η μ) (hηbound : ∀ᵐ x ∂μ, ‖η x‖ ≤ K)
    (ha : ∀ i j, AEStronglyMeasurable (a i j) μ)
    (hb : ∀ i j, ∀ᵐ x ∂μ, ‖a i j x‖ ≤ C)
    (hg : ∀ i, MemLp (g i) 2 μ) (hd : ∀ i, MemLp (d i) 2 μ) :
    let v := fun i x => η x * ((u x + c)⁻¹ * g i x)
    Integrable (fun x => ∑ i, ∑ j, a i j x * v j x * v i x) μ ∧
    Integrable (fun x => ∑ i, ∑ j, a i j x * v j x * d i x) μ ∧
    Integrable (fun x => ∑ i, ∑ j, a i j x * d j x * d i x) μ := by
  have hv (i : ι) : MemLp (fun x => η x * ((u x + c)⁻¹ * g i x)) 2 μ :=
    memLp_two_mul_of_ae_bound hη (memLp_shifted_logarithmic_gradient hc hu hupos (hg i)) hηbound
  exact ⟨integrable_matrix_pairing ha hb hv hv,
    integrable_matrix_pairing ha hb hv hd,
    integrable_matrix_pairing ha hb hd hd⟩

end HeatKernel

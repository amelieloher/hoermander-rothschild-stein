-- Copyright (c) 2026 Scott Armstrong and Amélie Loher. All rights reserved.
-- Released under Apache 2.0 license as described in the file LICENSE.
module

public import HeatKernel.Moser.LogarithmicFluxIntegrability
import all Mathlib.Basic.Real.Basic

/-! # Separating the integrable logarithmic principal and mixed fluxes -/

@[expose] public section
set_option autoImplicit false
set_option relaxedAutoImplicit false
noncomputable section
open MeasureTheory
namespace HeatKernel

/-- Square-integrable gradients make each row of the reciprocal coefficient flux
integrable, so the finite diffusion sum commutes with integration. -/
theorem sum_integral_shifted_logarithmic_flux_eq {α ι : Type*}
    [MeasurableSpace α] [Fintype ι] {μ : Measure α}
    {a : ι → ι → α → ℝ} {u η : α → ℝ} {g d : ι → α → ℝ} {c C K : ℝ}
    (hc : 0 < c) (hu : AEStronglyMeasurable u μ) (hupos : ∀ᵐ x ∂μ, 0 ≤ u x)
    (hη : AEStronglyMeasurable η μ) (hηbound : ∀ᵐ x ∂μ, ‖η x‖ ≤ K)
    (ha : ∀ i j, AEStronglyMeasurable (a i j) μ)
    (hb : ∀ i j, ∀ᵐ x ∂μ, ‖a i j x‖ ≤ C)
    (hg : ∀ i, MemLp (g i) 2 μ) (hd : ∀ i, MemLp (d i) 2 μ) :
    (∑ i, ∫ x, (∑ j, a i j x * g j x) *
      (η x ^ 2 * (-((u x + c) ^ 2)⁻¹ * g i x) +
        (2 * η x * d i x) * (u x + c)⁻¹) ∂μ) =
    ∫ x, ∑ i, ∑ j, a i j x * g j x *
      (η x ^ 2 * (-((u x + c) ^ 2)⁻¹ * g i x) +
        (2 * η x * d i x) * (u x + c)⁻¹) ∂μ := by
  let v := fun i x => η x * ((u x + c)⁻¹ * g i x)
  have hv (i : ι) : MemLp (v i) 2 μ :=
    memLp_two_mul_of_ae_bound hη (memLp_shifted_logarithmic_gradient hc hu hupos (hg i)) hηbound
  have he (i j : ι) (x : α) :
      a i j x * g j x *
        (η x ^ 2 * (-((u x + c) ^ 2)⁻¹ * g i x) +
          (2 * η x * d i x) * (u x + c)⁻¹) =
      -(a i j x * v j x * v i x) + 2 * (a i j x * v j x * d i x) := by
    dsimp only [v]
    rw [← inv_pow]
    ring
  have hint (i : ι) : Integrable (fun x => ∑ j, a i j x * g j x *
      (η x ^ 2 * (-((u x + c) ^ 2)⁻¹ * g i x) +
        (2 * η x * d i x) * (u x + c)⁻¹)) μ := by
    apply integrable_finsetSum
    intro j _
    simp_rw [he]
    exact ((memLp_two_mul_of_ae_bound (ha i j) (hv j) (hb i j)).integrable_mul
      (hv i)).neg.add (((memLp_two_mul_of_ae_bound (ha i j) (hv j) (hb i j)).integrable_mul
        (hd i)).const_mul 2)
  simp_rw [Finset.sum_mul]
  exact (integral_finsetSum _ (fun i _ => hint i)).symm

/-- The square-cutoff reciprocal flux is the negative logarithmic principal energy
plus twice the mixed cutoff flux. Square-integrability and coefficient bounds
justify the integral separation, without assumed integrability of either density. -/
theorem integral_shifted_logarithmic_flux_eq {α ι : Type*}
    [MeasurableSpace α] [Fintype ι] {μ : Measure α}
    {a : ι → ι → α → ℝ} {u η : α → ℝ} {g d : ι → α → ℝ} {c C K : ℝ}
    (hc : 0 < c) (hu : AEStronglyMeasurable u μ) (hupos : ∀ᵐ x ∂μ, 0 ≤ u x)
    (hη : AEStronglyMeasurable η μ) (hηbound : ∀ᵐ x ∂μ, ‖η x‖ ≤ K)
    (ha : ∀ i j, AEStronglyMeasurable (a i j) μ)
    (hb : ∀ i j, ∀ᵐ x ∂μ, ‖a i j x‖ ≤ C)
    (hg : ∀ i, MemLp (g i) 2 μ) (hd : ∀ i, MemLp (d i) 2 μ) :
    let v := fun i x => η x * ((u x + c)⁻¹ * g i x)
    (∫ x, ∑ i, ∑ j, a i j x * g j x *
      (η x ^ 2 * (-((u x + c) ^ 2)⁻¹ * g i x) +
        (2 * η x * d i x) * (u x + c)⁻¹) ∂μ) =
      -(∫ x, ∑ i, ∑ j, a i j x * v j x * v i x ∂μ) +
        2 * (∫ x, ∑ i, ∑ j, a i j x * v j x * d i x ∂μ) := by
  let v := fun i x => η x * ((u x + c)⁻¹ * g i x)
  obtain ⟨hprincipal, hmixed, _⟩ :=
    integrable_shifted_logarithmic_flux_terms hc hu hupos hη hηbound ha hb hg hd
  have he (x : α) :
      (∑ i, ∑ j, a i j x * g j x *
        (η x ^ 2 * (-((u x + c) ^ 2)⁻¹ * g i x) +
          (2 * η x * d i x) * (u x + c)⁻¹)) =
      -(∑ i, ∑ j, a i j x * v j x * v i x) +
        2 * (∑ i, ∑ j, a i j x * v j x * d i x) := by
    calc
      _ = ∑ i, ∑ j, (-(a i j x * v j x * v i x) +
          2 * (a i j x * v j x * d i x)) := by
        apply Finset.sum_congr rfl
        intro i _
        apply Finset.sum_congr rfl
        intro j _
        dsimp only [v]
        rw [← inv_pow]
        ring
      _ = _ := by
        simp only [Finset.sum_add_distrib, Finset.sum_neg_distrib, Finset.mul_sum]
  simp_rw [he]
  have hi := integral_add hprincipal.neg (hmixed.const_mul 2)
  simp only [Pi.neg_def] at hi
  rw [hi, integral_neg, integral_const_mul]

end HeatKernel

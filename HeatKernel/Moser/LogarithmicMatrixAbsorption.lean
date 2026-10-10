-- Copyright (c) 2026 Scott Armstrong and Amélie Loher. All rights reserved.
-- Released under Apache 2.0 license as described in the file LICENSE.
module

public import HeatKernel.Moser.LogarithmicFluxDecomposition
public import HeatKernel.Form.Ellipticity
import Mathlib.Tactic
import all Mathlib.Basic.Real.Basic

/-! # Matrix absorption of the integrable logarithmic reciprocal flux -/

@[expose] public section
set_option autoImplicit false
set_option relaxedAutoImplicit false
noncomputable section
open MeasureTheory
namespace HeatKernel

/-- Symmetry and positivity of a finite matrix absorb the mixed cutoff pairing. -/
theorem logarithmic_matrix_absorption {ι : Type*} [Fintype ι]
    (a : ι → ι → ℝ) (hsym : ∀ i j, a i j = a j i)
    (hpos : ∀ ξ, 0 ≤ matrixEnergy a ξ) (v d : ι → ℝ) :
    matrixEnergy a v / 2 - 2 * matrixEnergy a d ≤
      matrixEnergy a v - 2 * (∑ i, ∑ j, a i j * v j * d i) := by
  have hcross : (∑ i, ∑ j, a i j * d j * v i) =
      ∑ i, ∑ j, a i j * v j * d i := by
    rw [Finset.sum_comm]
    apply Finset.sum_congr rfl
    intro i _
    apply Finset.sum_congr rfl
    intro j _
    rw [hsym j i]
    ring
  have hexp : matrixEnergy a (fun i => v i - 2 * d i) =
      matrixEnergy a v - 2 * (∑ i, ∑ j, a i j * v j * d i) -
        2 * (∑ i, ∑ j, a i j * d j * v i) + 4 * matrixEnergy a d := by
    unfold matrixEnergy
    calc
      _ = ∑ i, ∑ j, (a i j * v j * v i - 2 * (a i j * v j * d i) -
          2 * (a i j * d j * v i) + 4 * (a i j * d j * d i)) := by
        apply Finset.sum_congr rfl
        intro i _
        apply Finset.sum_congr rfl
        intro j _
        ring
      _ = _ := by
        simp only [Finset.sum_add_distrib, Finset.sum_sub_distrib, Finset.mul_sum]
  have hp := hpos (fun i => v i - 2 * d i)
  rw [hexp, hcross] at hp
  linarith

/-- The actual square-cutoff reciprocal flux controls half the logarithmic matrix
energy. Original L² gradients and bounded coefficients supply all integrability. -/
theorem integral_shifted_logarithmic_flux_absorption {α ι : Type*}
    [MeasurableSpace α] [Fintype ι] {μ : Measure α}
    {a : ι → ι → α → ℝ} {u η : α → ℝ} {g d : ι → α → ℝ} {c C K : ℝ}
    (hc : 0 < c) (hu : AEStronglyMeasurable u μ) (hupos : ∀ᵐ x ∂μ, 0 ≤ u x)
    (hη : AEStronglyMeasurable η μ) (hηbound : ∀ᵐ x ∂μ, ‖η x‖ ≤ K)
    (ha : ∀ i j, AEStronglyMeasurable (a i j) μ)
    (hb : ∀ i j, ∀ᵐ x ∂μ, ‖a i j x‖ ≤ C)
    (hg : ∀ i, MemLp (g i) 2 μ) (hd : ∀ i, MemLp (d i) 2 μ)
    (hsym : ∀ᵐ x ∂μ, ∀ i j, a i j x = a j i x)
    (hpos : ∀ᵐ x ∂μ, ∀ ξ, 0 ≤ matrixEnergy (fun i j => a i j x) ξ) :
    let v := fun i x => η x * ((u x + c)⁻¹ * g i x)
    (∫ x, ∑ i, ∑ j, a i j x * v j x * v i x ∂μ) / 2 ≤
      -(∫ x, ∑ i, ∑ j, a i j x * g j x *
        (η x ^ 2 * (-((u x + c) ^ 2)⁻¹ * g i x) +
          (2 * η x * d i x) * (u x + c)⁻¹) ∂μ) +
        2 * (∫ x, ∑ i, ∑ j, a i j x * d j x * d i x ∂μ) := by
  obtain ⟨hp, hm, hd'⟩ :=
    integrable_shifted_logarithmic_flux_terms hc hu hupos hη hηbound ha hb hg hd
  have hi := integral_mono_ae ((hp.div_const 2).sub (hd'.const_mul 2))
    (hp.sub (hm.const_mul 2)) (by
      filter_upwards [hsym, hpos] with x hs hx
      exact logarithmic_matrix_absorption (fun i j => a i j x) hs hx
        (fun i => η x * ((u x + c)⁻¹ * g i x)) (fun i => d i x))
  simp only [Pi.sub_def, integral_sub (hp.div_const 2) (hd'.const_mul 2),
    integral_sub hp (hm.const_mul 2), integral_div, integral_const_mul] at hi
  have he := integral_shifted_logarithmic_flux_eq hc hu hupos hη hηbound ha hb hg hd
  dsimp only at he ⊢
  linarith

end HeatKernel

-- Copyright (c) 2026 Scott Armstrong and Amélie Loher. All rights reserved.
-- Released under Apache 2.0 license as described in the file LICENSE.
module

public import HeatKernel.Form.CoefficientContinuity
public import HeatKernel.Form.ContinuouslyDifferentiableComposition
import Mathlib.Tactic.Linter

/-! # Coefficient energy under differentiable scalar contractions -/

@[expose] public section

noncomputable section

open Set MeasureTheory TopologicalSpace

namespace HeatKernel

variable {N q : ℕ} (U : Opens (Fin N → ℝ))
    (X : Fin q → (Fin N → ℝ) → (Fin N → ℝ))
    (a : Fin q → Fin q → (Fin N → ℝ) → ℝ) {lower upper : ℝ}
    (hlower : 0 ≤ lower)
    (ha : ∀ i j, AEStronglyMeasurable (a i j) (volume.restrict (U : Set (Fin N → ℝ))))
    (hsym : ∀ᵐ x ∂volume.restrict (U : Set (Fin N → ℝ)), ∀ i j, a i j x = a j i x)
    (hbound : ∀ᵐ x ∂volume.restrict (U : Set (Fin N → ℝ)), ∀ ξ : Fin q → ℝ,
      lower * coordinateNormSq ξ ≤ matrixEnergy (fun i j => a i j x) ξ ∧
      matrixEnergy (fun i j => a i j x) ξ ≤ upper * coordinateNormSq ξ)

include hlower ha hsym hbound in
/-- Multiplying every gradient component by the same scalar of modulus at most one decreases
any positive measurable matrix energy. -/
theorem coefficientEnergy_self_le_of_scalar_gradient (u z : energyGraph U X) (b : (Fin N → ℝ) → ℝ)
    (hb : ∀ᵐ x ∂volume.restrict (U : Set (Fin N → ℝ)), ‖b x‖ ≤ 1)
    (hz : ∀ i, (z : GradientSpace U q).snd i =ᵐ[volume.restrict (U : Set (Fin N → ℝ))]
      fun x => b x * (u : GradientSpace U q).snd i x) :
    coefficientEnergy U X a z z ≤ coefficientEnergy U X a u u := by
  have hentry := ae_norm_coefficient_entry_le U a hlower hsym hbound
  apply integral_mono_ae (integrable_coefficientEnergyDensity U X a z z ha hentry)
    (integrable_coefficientEnergyDensity U X a u u ha hentry)
  filter_upwards [hb, hbound, ae_all_iff.mpr hz] with x hbx hx hzx
  have heq : coefficientEnergyDensity U X a z z x =
      (b x) ^ 2 * coefficientEnergyDensity U X a u u x := by
    unfold coefficientEnergyDensity
    simp only [hzx, Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro i _
    apply Finset.sum_congr rfl
    intro j _
    ring
  rw [heq]
  have hp : 0 ≤ coefficientEnergyDensity U X a u u x := by
    exact (mul_nonneg hlower (Finset.sum_nonneg fun _ _ => sq_nonneg _)).trans
      (hx (fun i => (u : GradientSpace U q).snd i x)).1
  have hb' : (b x) ^ 2 ≤ 1 := by
    have H := (sq_le_sq₀ (norm_nonneg (b x)) (by norm_num : (0 : ℝ) ≤ 1)).mpr hbx
    simpa only [Real.norm_eq_abs, sq_abs, one_pow] using H
  simpa only [one_mul] using mul_le_mul_of_nonneg_right hb' hp


end HeatKernel

-- Copyright (c) 2026 Scott Armstrong and Amélie Loher. All rights reserved.
-- Released under Apache 2.0 license as described in the file LICENSE.
module

public import HeatKernel.Form.CoefficientEnergy
import Mathlib.Tactic.Linter

/-! # Bilinearity of measurable-coefficient horizontal energy -/

@[expose] public section

noncomputable section

open Set MeasureTheory TopologicalSpace

namespace HeatKernel

variable {N q : ℕ} (U : Opens (Fin N → ℝ))
    (X : Fin q → (Fin N → ℝ) → (Fin N → ℝ))
    (a : Fin q → Fin q → (Fin N → ℝ) → ℝ) {C : ℝ}
    (ha : ∀ i j, AEStronglyMeasurable (a i j) (volume.restrict (U : Set (Fin N → ℝ))))
    (hb : ∀ i j, ∀ᵐ x ∂volume.restrict (U : Set (Fin N → ℝ)), ‖a i j x‖ ≤ C)

include ha hb in
/-- Coefficient energy is additive in the first function. -/
theorem coefficientEnergy_add_left (u v w : energyGraph U X) :
    coefficientEnergy U X a (u + v) w = coefficientEnergy U X a u w + coefficientEnergy U X a v w := by
  have hadd : ∀ i, ((u + v : energyGraph U X) : GradientSpace U q).snd i
      =ᵐ[volume.restrict (U : Set (Fin N → ℝ))]
      fun x => (u : GradientSpace U q).snd i x + (v : GradientSpace U q).snd i x := by
    intro i
    simpa only [Submodule.coe_add, WithLp.add_snd, PiLp.add_apply, Pi.add_def] using
      Lp.coeFn_add ((u : GradientSpace U q).snd i) ((v : GradientSpace U q).snd i)
  have H : coefficientEnergyDensity U X a (u + v) w
      =ᵐ[volume.restrict (U : Set (Fin N → ℝ))]
      fun x => coefficientEnergyDensity U X a u w x + coefficientEnergyDensity U X a v w x := by
    filter_upwards [ae_all_iff.mpr hadd] with x hx
    simp only [coefficientEnergyDensity, hx, mul_add, add_mul, Finset.sum_add_distrib]
  unfold coefficientEnergy
  rw [integral_congr_ae H, integral_add
    (integrable_coefficientEnergyDensity U X a u w ha hb)
    (integrable_coefficientEnergyDensity U X a v w ha hb)]

/-- Coefficient energy is real linear in the first function. -/
theorem coefficientEnergy_smul_left (r : ℝ) (u v : energyGraph U X) :
    coefficientEnergy U X a (r • u) v = r * coefficientEnergy U X a u v := by
  have hsmul : ∀ i, ((r • u : energyGraph U X) : GradientSpace U q).snd i
      =ᵐ[volume.restrict (U : Set (Fin N → ℝ))]
      fun x => r * (u : GradientSpace U q).snd i x := by
    intro i
    simpa only [Submodule.coe_smul, WithLp.smul_snd, PiLp.smul_apply, Pi.smul_def, smul_eq_mul] using
      Lp.coeFn_smul r ((u : GradientSpace U q).snd i)
  have H : coefficientEnergyDensity U X a (r • u) v
      =ᵐ[volume.restrict (U : Set (Fin N → ℝ))]
      fun x => r * coefficientEnergyDensity U X a u v x := by
    filter_upwards [ae_all_iff.mpr hsmul] with x hx
    simp only [coefficientEnergyDensity, hx, Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro i _
    apply Finset.sum_congr rfl
    intro j _
    ring
  unfold coefficientEnergy
  rw [integral_congr_ae H, integral_const_mul]

include ha hb in
/-- Symmetry and additivity give additivity in the second function. -/
theorem coefficientEnergy_add_right
    (hsym : ∀ i j, ∀ᵐ x ∂volume.restrict (U : Set (Fin N → ℝ)), a i j x = a j i x)
    (u v w : energyGraph U X) :
    coefficientEnergy U X a u (v + w) = coefficientEnergy U X a u v + coefficientEnergy U X a u w := by
  rw [coefficientEnergy_symm U X a u (v + w) hsym,
    coefficientEnergy_add_left U X a ha hb,
    coefficientEnergy_symm U X a v u hsym, coefficientEnergy_symm U X a w u hsym]

/-- Symmetry and real linearity give real linearity in the second function. -/
theorem coefficientEnergy_smul_right
    (hsym : ∀ i j, ∀ᵐ x ∂volume.restrict (U : Set (Fin N → ℝ)), a i j x = a j i x)
    (r : ℝ) (u v : energyGraph U X) :
    coefficientEnergy U X a u (r • v) = r * coefficientEnergy U X a u v := by
  rw [coefficientEnergy_symm U X a u (r • v) hsym,
    coefficientEnergy_smul_left U X a,
    coefficientEnergy_symm U X a v u hsym]


end HeatKernel

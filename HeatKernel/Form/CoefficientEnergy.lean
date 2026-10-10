-- Copyright (c) 2026 Scott Armstrong and Amélie Loher. All rights reserved.
-- Released under Apache 2.0 license as described in the file LICENSE.
module

public import HeatKernel.Form.EnergyDensity
public import HeatKernel.Form.MatrixCoefficientBounds
public import HeatKernel.Moser.JointMeasurability

import Mathlib.Tactic.Linter

/-! # Horizontal energy forms with measurable matrix coefficients -/

@[expose] public section

noncomputable section

open Set MeasureTheory TopologicalSpace

namespace HeatKernel

variable {N q : ℕ} (U : Opens (Fin N → ℝ))
    (X : Fin q → (Fin N → ℝ) → (Fin N → ℝ))
    (a : Fin q → Fin q → (Fin N → ℝ) → ℝ)

/-- The scalar density of a horizontal form with matrix coefficients. -/
def coefficientEnergyDensity (u v : energyGraph U X) (x : Fin N → ℝ) : ℝ :=
  ∑ i, ∑ j, a i j x * (u : GradientSpace U q).snd j x * (v : GradientSpace U q).snd i x

/-- The horizontal form with measurable matrix coefficients. -/
def coefficientEnergy (u v : energyGraph U X) : ℝ :=
  ∫ x, coefficientEnergyDensity U X a u v x ∂volume.restrict (U : Set (Fin N → ℝ))

/-- Bounded measurable entries give an integrable coefficient energy density. -/
theorem integrable_coefficientEnergyDensity (u v : energyGraph U X) {C : ℝ}
    (ha : ∀ i j, AEStronglyMeasurable (a i j) (volume.restrict (U : Set (Fin N → ℝ))))
    (hb : ∀ i j, ∀ᵐ x ∂volume.restrict (U : Set (Fin N → ℝ)), ‖a i j x‖ ≤ C) :
    Integrable (coefficientEnergyDensity U X a u v) (volume.restrict (U : Set (Fin N → ℝ))) := by
  apply integrable_finsetSum
  intro i _
  apply integrable_finsetSum
  intro j _
  have hm := memLp_two_mul_of_ae_bound (ha i j) (Lp.memLp ((u : GradientSpace U q).snd j)) (hb i j)
  simpa only [Pi.mul_def] using hm.integrable_mul (Lp.memLp ((v : GradientSpace U q).snd i))

/-- Symmetric matrix coefficients give a symmetric horizontal form. -/
theorem coefficientEnergy_symm (u v : energyGraph U X)
    (hsym : ∀ i j, ∀ᵐ x ∂volume.restrict (U : Set (Fin N → ℝ)), a i j x = a j i x) :
    coefficientEnergy U X a u v = coefficientEnergy U X a v u := by
  apply integral_congr_ae
  filter_upwards [ae_all_iff.mpr (fun i => ae_all_iff.mpr (hsym i))] with x hx
  dsimp only [coefficientEnergyDensity]
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro i _
  apply Finset.sum_congr rfl
  intro j _
  rw [hx j i]
  ring

/-- Elliptic matrix bounds compare the measurable-coefficient energy to horizontal energy. -/
theorem coefficientEnergy_self_bounds (u : energyGraph U X) {lower upper : ℝ} (hlower : 0 ≤ lower)
    (ha : ∀ i j, AEStronglyMeasurable (a i j) (volume.restrict (U : Set (Fin N → ℝ))))
    (hsym : ∀ᵐ x ∂volume.restrict (U : Set (Fin N → ℝ)), ∀ i j, a i j x = a j i x)
    (hbound : ∀ᵐ x ∂volume.restrict (U : Set (Fin N → ℝ)), ∀ ξ : Fin q → ℝ,
      lower * coordinateNormSq ξ ≤ matrixEnergy (fun i j => a i j x) ξ ∧
      matrixEnergy (fun i j => a i j x) ξ ≤ upper * coordinateNormSq ξ) :
    lower * horizontalEnergy U X u u ≤ coefficientEnergy U X a u u ∧
      coefficientEnergy U X a u u ≤ upper * horizontalEnergy U X u u := by
  have hb : ∀ i j, ∀ᵐ x ∂volume.restrict (U : Set (Fin N → ℝ)), ‖a i j x‖ ≤ upper := by
    intro i j
    filter_upwards [hsym, hbound] with x hs hx
    exact norm_matrix_entry_le_of_elliptic_bounds (fun i j => a i j x) hlower hs hx i j
  have hi := integrable_coefficientEnergyDensity U X a u u ha hb
  have H : ∀ᵐ x ∂volume.restrict (U : Set (Fin N → ℝ)),
      lower * horizontalEnergyDensity U X u u x ≤ coefficientEnergyDensity U X a u u x ∧
      coefficientEnergyDensity U X a u u x ≤ upper * horizontalEnergyDensity U X u u x := by
    filter_upwards [hbound] with x hx
    simpa only [coordinateNormSq, matrixEnergy, coefficientEnergyDensity,
      horizontalEnergyDensity, pow_two] using hx (fun i => (u : GradientSpace U q).snd i x)
  have hlo := integral_mono_ae ((integrable_horizontalEnergyDensity U X u u).const_mul lower) hi
    (H.mono fun _ hx => hx.1)
  have hhi := integral_mono_ae hi ((integrable_horizontalEnergyDensity U X u u).const_mul upper)
    (H.mono fun _ hx => hx.2)
  rw [integral_const_mul, ← horizontalEnergy_eq_integral_density] at hlo hhi
  exact ⟨hlo, hhi⟩

end HeatKernel

-- Copyright (c) 2026 Scott Armstrong and Amélie Loher. All rights reserved.
-- Released under Apache 2.0 license as described in the file LICENSE.
module

public import HeatKernel.Form.CoefficientBilinearity
public import Mathlib.Analysis.Normed.Operator.Bilinear
import Mathlib.Tactic.Linter

/-! # Continuous bilinear realization of elliptic horizontal forms -/

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

include hlower hsym hbound in
/-- Ellipticity gives one uniform almost-everywhere entry bound. -/
theorem ae_norm_coefficient_entry_le (i j : Fin q) :
    ∀ᵐ x ∂volume.restrict (U : Set (Fin N → ℝ)), ‖a i j x‖ ≤ upper := by
  filter_upwards [hsym, hbound] with x hs hx
  exact norm_matrix_entry_le_of_elliptic_bounds (fun i j => a i j x) hlower hs hx i j

/-- The measurable-coefficient form is a positive semidefinite scalar product on the
horizontal graph domain, without changing its given norm. -/
@[instance_reducible] def coefficientEnergyCore : PreInnerProductSpace.Core ℝ (energyGraph U X) where
  inner := coefficientEnergy U X a
  conj_inner_symm u v := by
    simpa only [conj_trivial] using coefficientEnergy_symm U X a v u
      (fun i j => hsym.mono fun _ hx => hx i j)
  re_inner_nonneg u := by
    change 0 ≤ coefficientEnergy U X a u u
    exact (mul_nonneg hlower (horizontalEnergy_self_nonneg U X u)).trans
      (coefficientEnergy_self_bounds U X a u hlower ha hsym hbound).1
  add_left u v w := coefficientEnergy_add_left U X a ha
    (ae_norm_coefficient_entry_le U a hlower hsym hbound) u v w
  smul_left u v r := by
    simpa only [conj_trivial] using coefficientEnergy_smul_left U X a r u v

include hlower ha hsym hbound in
/-- Cauchy–Schwarz for the measurable-coefficient horizontal form. -/
theorem norm_coefficientEnergy_sq_le (u v : energyGraph U X) :
    ‖coefficientEnergy U X a u v‖ ^ 2 ≤
      coefficientEnergy U X a u u * coefficientEnergy U X a v v := by
  let := coefficientEnergyCore U X a hlower ha hsym hbound
  have H := InnerProductSpace.Core.inner_mul_inner_self_le (𝕜 := ℝ) u v
  change ‖coefficientEnergy U X a u v‖ * ‖coefficientEnergy U X a v u‖ ≤
    coefficientEnergy U X a u u * coefficientEnergy U X a v v at H
  rw [coefficientEnergy_symm U X a v u (fun i j => hsym.mono fun _ hx => hx i j)] at H
  simpa only [pow_two] using H

include hlower ha hsym hbound in
/-- The coefficient form is bounded in the horizontal graph norm. -/
theorem norm_coefficientEnergy_le (hupper : 0 ≤ upper) (u v : energyGraph U X) :
    ‖coefficientEnergy U X a u v‖ ≤ upper * ‖u‖ * ‖v‖ := by
  have he : ∀ z : energyGraph U X, 0 ≤ coefficientEnergy U X a z z ∧
      coefficientEnergy U X a z z ≤ upper * ‖z‖ ^ 2 := by
    intro z
    obtain ⟨hlo, hhi⟩ := coefficientEnergy_self_bounds U X a z hlower ha hsym hbound
    refine ⟨(mul_nonneg hlower (horizontalEnergy_self_nonneg U X z)).trans hlo, hhi.trans ?_⟩
    apply mul_le_mul_of_nonneg_left _ hupper
    rw [energyGraph_norm_sq_eq]
    exact le_add_of_nonneg_left (sq_nonneg _)
  apply (sq_le_sq₀ (norm_nonneg _) (by positivity : 0 ≤ upper * ‖u‖ * ‖v‖)).mp
  calc
    _ ≤ coefficientEnergy U X a u u * coefficientEnergy U X a v v :=
      norm_coefficientEnergy_sq_le U X a hlower ha hsym hbound u v
    _ ≤ (upper * ‖u‖ ^ 2) * (upper * ‖v‖ ^ 2) :=
      mul_le_mul (he u).2 (he v).2 (he v).1 (by positivity)
    _ = _ := by ring

/-- The coefficient form as a continuous bilinear map on the common energy domain. -/
def coefficientEnergyContinuousBilinear (hupper : 0 ≤ upper) :
    energyGraph U X →L[ℝ] energyGraph U X →L[ℝ] ℝ :=
  (LinearMap.mk₂ ℝ (coefficientEnergy U X a)
    (coefficientEnergy_add_left U X a ha (ae_norm_coefficient_entry_le U a hlower hsym hbound))
    (fun r u v => by
      simpa only [smul_eq_mul] using coefficientEnergy_smul_left U X a r u v)
    (coefficientEnergy_add_right U X a ha (ae_norm_coefficient_entry_le U a hlower hsym hbound)
      (fun i j => hsym.mono fun _ hx => hx i j))
    (fun r u v => by
      simpa only [smul_eq_mul] using coefficientEnergy_smul_right U X a
        (fun i j => hsym.mono fun _ hx => hx i j) r u v)).mkContinuous₂ upper
    (norm_coefficientEnergy_le U X a hlower ha hsym hbound hupper)

end HeatKernel

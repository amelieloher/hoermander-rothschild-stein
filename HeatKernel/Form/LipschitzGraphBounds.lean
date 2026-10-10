-- Copyright (c) 2026 Scott Armstrong and Amélie Loher. All rights reserved.
-- Released under Apache 2.0 license as described in the file LICENSE.
module

public import HeatKernel.Form.ZeroBoundaryLipschitz
public import HeatKernel.Form.ContractionGraphNorm
import Mathlib.Tactic.Linter

/-! # Graph norm bounds for Lipschitz scalar compositions -/

@[expose] public section

noncomputable section

open Set MeasureTheory Filter TopologicalSpace
open scoped NNReal

namespace HeatKernel

/-- Squared L² and energy bounds give the corresponding scaled graph norm bound. -/
theorem energyGraph_norm_le_mul_of_bounds {N q : ℕ} (U : Opens (Fin N → ℝ))
    (X : Fin q → (Fin N → ℝ) → (Fin N → ℝ)) (u v : energyGraph U X)
    {L : ℝ} (hL : 0 ≤ L) (hf : ‖energyInclusion U X u‖ ≤ L * ‖energyInclusion U X v‖)
    (he : horizontalEnergy U X u u ≤ L ^ 2 * horizontalEnergy U X v v) :
    ‖u‖ ≤ L * ‖v‖ := by
  apply (sq_le_sq₀ (norm_nonneg _) (mul_nonneg hL (norm_nonneg _))).mp
  rw [mul_pow, energyGraph_norm_sq_eq U X u, energyGraph_norm_sq_eq U X v, mul_add]
  exact add_le_add (by simpa only [mul_pow] using
    (sq_le_sq₀ (norm_nonneg _) (mul_nonneg hL (norm_nonneg _))).mpr hf) he

/-- A Lipschitz composition with its pointwise energy bound satisfies the exact graph norm bound. -/
theorem norm_energyGraph_comp_lipschitz_le {N q : ℕ}
    (X : Fin q → (Fin N → ℝ) → (Fin N → ℝ)) (u z : energyGraph (N := N) ⊤ X)
    {L : ℝ≥0} {η : ℝ → ℝ} (hη : LipschitzWith L η) (hzero : η 0 = 0)
    (hz : (z : GradientSpace (N := N) ⊤ q).fst =ᵐ[volume]
      (fun x => η ((u : GradientSpace (N := N) ⊤ q).fst x)))
    (he : ∀ᵐ x ∂volume, horizontalEnergyDensity ⊤ X z z x ≤
      (L : ℝ) ^ 2 * horizontalEnergyDensity ⊤ X u u x) : ‖z‖ ≤ (L : ℝ) * ‖u‖ := by
  apply energyGraph_norm_le_mul_of_bounds ⊤ X z u L.coe_nonneg
  · have heq : energyInclusion ⊤ X z = hη.compLp hzero (energyInclusion ⊤ X u) := by
      apply Lp.ext
      have H := hη.coeFn_compLp hzero (energyInclusion ⊤ X u)
      simp only [Opens.coe_top, Measure.restrict_univ] at H ⊢
      exact hz.trans H.symm
    rw [heq]
    exact hη.norm_compLp_le hzero _
  · rw [horizontalEnergy_eq_integral_density, horizontalEnergy_eq_integral_density,
      ← integral_const_mul]
    apply integral_mono_ae (integrable_horizontalEnergyDensity ⊤ X z z)
      ((integrable_horizontalEnergyDensity ⊤ X u u).const_mul _)
    simp only [Opens.coe_top, Measure.restrict_univ]
    filter_upwards [he] with x hx
    exact hx

/-- Every scalar Lipschitz map fixing zero has a representative satisfying its exact graph norm bound. -/
theorem exists_energyGraph_comp_lipschitz_norm_le {N q : ℕ}
    (X : Fin q → (Fin N → ℝ) → (Fin N → ℝ))
    (hX : ∀ i, ContDiff ℝ (⊤ : ℕ∞) (X i)) (u : energyGraph (N := N) ⊤ X)
    {L : ℝ≥0} {η : ℝ → ℝ} (hη : LipschitzWith L η) (hzero : η 0 = 0) :
    ∃ z : energyGraph (N := N) ⊤ X,
      ((z : GradientSpace (N := N) ⊤ q).fst =ᵐ[volume]
        (fun x => η ((u : GradientSpace (N := N) ⊤ q).fst x))) ∧ ‖z‖ ≤ (L : ℝ) * ‖u‖ := by
  obtain ⟨z, hz, he⟩ := exists_energyGraph_comp_lipschitz_density_le X hX u hη hzero
  exact ⟨z, hz, norm_energyGraph_comp_lipschitz_le X u z hη hzero hz he⟩

end HeatKernel

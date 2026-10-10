-- Copyright (c) 2026 Scott Armstrong and Amélie Loher. All rights reserved.
-- Released under Apache 2.0 license as described in the file LICENSE.
module

public import HeatKernel.Form.IndicatorCoefficients
public import HeatKernel.Form.CoefficientNormalContractions
public import Mathlib.MeasureTheory.Function.AEEqOfIntegral
import Mathlib.Tactic.Linter

/-! # Pointwise horizontal gradient bounds for normal contractions -/

@[expose] public section

noncomputable section

open Set MeasureTheory Filter TopologicalSpace
open scoped NNReal

namespace HeatKernel

/-- A normal contraction decreases the horizontal energy density almost everywhere. -/
theorem horizontalEnergyDensity_le_of_normalContraction {N q : ℕ}
    (X : Fin q → (Fin N → ℝ) → (Fin N → ℝ))
    (hX : ∀ i, ContDiff ℝ (⊤ : ℕ∞) (X i)) (u z : energyGraph (N := N) ⊤ X)
    {η : ℝ → ℝ} (hη : LipschitzWith 1 η) (hzero : η 0 = 0)
    (hz : energyInclusion ⊤ X z = hη.compLp hzero (energyInclusion ⊤ X u)) :
    ∀ᵐ x ∂volume, horizontalEnergyDensity ⊤ X z z x ≤ horizontalEnergyDensity ⊤ X u u x := by
  have hi : ∀ v : energyGraph (N := N) ⊤ X, Integrable (horizontalEnergyDensity ⊤ X v v) volume := by
    intro v
    simpa only [Opens.coe_top, Measure.restrict_univ] using integrable_horizontalEnergyDensity ⊤ X v v
  apply ae_le_of_forall_setIntegral_le (hi z) (hi u)
  intro s hs _
  obtain ⟨w, hw, he⟩ := exists_energyGraph_comp_normalContraction_coefficient X hX
    (indicatorMatrix s) (lower := 0) (upper := 1) (by norm_num) (by norm_num)
    (aestronglyMeasurable_indicatorMatrix hs)
    (Eventually.of_forall fun x => indicatorMatrix_symm s x)
    (Eventually.of_forall fun x ξ => matrixEnergy_indicatorMatrix_bounds s x ξ)
    u hη hzero
  have hwz : w = z := energyInclusion_injective ⊤ X (fun i => (hX i).contDiffOn) (hw.trans hz.symm)
  rw [hwz, coefficientEnergy_indicatorMatrix X hs, coefficientEnergy_indicatorMatrix X hs] at he
  exact he

/-- Normal contractions have energy representatives with the pointwise horizontal density bound. -/
theorem exists_energyGraph_comp_normalContraction_density_le {N q : ℕ}
    (X : Fin q → (Fin N → ℝ) → (Fin N → ℝ))
    (hX : ∀ i, ContDiff ℝ (⊤ : ℕ∞) (X i)) (u : energyGraph (N := N) ⊤ X)
    {η : ℝ → ℝ} (hη : LipschitzWith 1 η) (hzero : η 0 = 0) :
    ∃ z : energyGraph (N := N) ⊤ X,
      energyInclusion ⊤ X z = hη.compLp hzero (energyInclusion ⊤ X u) ∧
      ∀ᵐ x ∂volume, horizontalEnergyDensity ⊤ X z z x ≤ horizontalEnergyDensity ⊤ X u u x := by
  obtain ⟨z, hz, _⟩ := exists_energyGraph_comp_normalContraction X hX u hη hzero
  exact ⟨z, hz, horizontalEnergyDensity_le_of_normalContraction X hX u z hη hzero hz⟩



end HeatKernel

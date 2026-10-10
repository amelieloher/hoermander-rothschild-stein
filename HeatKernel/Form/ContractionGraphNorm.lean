-- Copyright (c) 2026 Scott Armstrong and Amélie Loher. All rights reserved.
-- Released under Apache 2.0 license as described in the file LICENSE.
module

public import HeatKernel.Form.NormalContractions
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Linter

/-! # Graph norm bounds for normal contractions -/

@[expose] public section

noncomputable section

open Set MeasureTheory TopologicalSpace
open scoped NNReal

namespace HeatKernel

/-- Decreasing both the function norm and horizontal energy decreases the graph norm. -/
theorem energyGraph_norm_le_of_bounds {N q : ℕ} (U : Opens (Fin N → ℝ))
    (X : Fin q → (Fin N → ℝ) → (Fin N → ℝ)) (u v : energyGraph U X)
    (hf : ‖energyInclusion U X u‖ ≤ ‖energyInclusion U X v‖)
    (he : horizontalEnergy U X u u ≤ horizontalEnergy U X v v) : ‖u‖ ≤ ‖v‖ := by
  apply (sq_le_sq₀ (norm_nonneg _) (norm_nonneg _)).mp
  rw [energyGraph_norm_sq_eq, energyGraph_norm_sq_eq]
  exact add_le_add ((sq_le_sq₀ (norm_nonneg _) (norm_nonneg _)).mpr hf) he

/-- Normal scalar contractions fixing zero do not increase the L² norm. -/
theorem norm_compLp_normalContraction_le {α : Type*} [MeasurableSpace α] {μ : Measure α}
    {η : ℝ → ℝ} (hη : LipschitzWith 1 η) (hzero : η 0 = 0) (u : Lp ℝ 2 μ) :
    ‖hη.compLp hzero u‖ ≤ ‖u‖ := by
  apply Lp.norm_le_norm_of_ae_le
  filter_upwards [hη.coeFn_compLp hzero u] with x hx
  rw [hx]
  simpa only [Function.comp_def, hzero, dist_zero_right, NNReal.coe_one, one_mul] using hη.dist_le_mul (u x) 0

/-- A normal contraction has an energy-domain representative with no larger graph norm. -/
theorem exists_energyGraph_comp_normalContraction_norm_le {N q : ℕ}
    (X : Fin q → (Fin N → ℝ) → (Fin N → ℝ))
    (hX : ∀ i, ContDiff ℝ (⊤ : ℕ∞) (X i)) (u : energyGraph (N := N) ⊤ X)
    {η : ℝ → ℝ} (hη : LipschitzWith 1 η) (hzero : η 0 = 0) :
    ∃ z : energyGraph (N := N) ⊤ X,
      energyInclusion ⊤ X z = hη.compLp hzero (energyInclusion ⊤ X u) ∧ ‖z‖ ≤ ‖u‖ := by
  obtain ⟨z, hz, he⟩ := exists_energyGraph_comp_normalContraction X hX u hη hzero
  refine ⟨z, hz, energyGraph_norm_le_of_bounds ⊤ X z u ?_ he⟩
  rw [hz]
  exact norm_compLp_normalContraction_le hη hzero _


end HeatKernel

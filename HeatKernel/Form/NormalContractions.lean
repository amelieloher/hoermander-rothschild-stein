-- Copyright (c) 2026 Scott Armstrong and Amélie Loher. All rights reserved.
-- Released under Apache 2.0 license as described in the file LICENSE.
module

public import HeatKernel.Form.ContractionLimits
public import HeatKernel.Form.ScalarContractionApproximation

/-!
# Normal contractions of the horizontal energy domain

Every scalar contraction fixing zero preserves the closed horizontal energy domain and does
not increase energy. This includes the truncation to the interval from zero to one.
-/

@[expose] public section

noncomputable section

open MeasureTheory TopologicalSpace
open scoped NNReal

namespace HeatKernel

/-- Normal contractions preserve the global energy domain and decrease horizontal energy. -/
theorem exists_energyGraph_comp_normalContraction {N q : ℕ}
    (X : Fin q → (Fin N → ℝ) → (Fin N → ℝ))
    (hX : ∀ i, ContDiff ℝ (⊤ : ℕ∞) (X i))
    (v : energyGraph (N := N) ⊤ X) {η : ℝ → ℝ}
    (hη : LipschitzWith 1 η) (hzero : η 0 = 0) :
    ∃ z : energyGraph (N := N) ⊤ X,
      energyInclusion ⊤ X z = hη.compLp hzero (energyInclusion ⊤ X v) ∧
      horizontalEnergy ⊤ X z z ≤ horizontalEnergy ⊤ X v v := by
  obtain ⟨a, ha, ha0, hab, hat⟩ := exists_smooth_contraction_approximation hη hzero
  exact exists_energyGraph_comp_of_contDiff_approximation X hX v hη hzero
    (fun n => (ha n).of_le (by simp)) ha0 hab hat

end HeatKernel

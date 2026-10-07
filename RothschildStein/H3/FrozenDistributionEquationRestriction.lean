-- Copyright (c) 2026 Scott Armstrong and Amélie Loher. All rights reserved.
-- Released under Apache 2.0 license as described in the file LICENSE.
module

public import RothschildStein.H3.FrozenDriftEquationPatch
public import RothschildStein.H3.FrozenDriftEquationBridge
public import RothschildStein.S.DistributionRestriction

set_option autoImplicit false
set_option relaxedAutoImplicit false
@[expose] public section
noncomputable section
open Set TopologicalSpace
namespace RothschildStein.H3

/-- The actual fixed equation of an arbitrary distribution
restricts to each interior open patch through the shared test extension. -/
theorem frozen_distribution_drift_equation_restrict {N q : ℕ}
    (Ω V : Opens (Fin N → ℝ)) (hV : V ≤ Ω)
    (X : Fin (q + 1) → (Fin N → ℝ) → (Fin N → ℝ))
    (hX : ∀ i, ContDiffOn ℝ (⊤ : ℕ∞) (X i) (Ω : Set (Fin N → ℝ)))
    (T : Distribution Ω ℝ (⊤ : ℕ∞)) (f : (Fin N → ℝ) → ℝ)
    (heq : hasDistributionEquationWithDrift Ω X hX T f) :
    hasDistributionEquationWithDrift V X (fun i => (hX i).mono hV)
      (RothschildStein.S.distributionRestrictionCLM Ω V T) f := by
  refine ⟨heq.1.mono_set hV, ?_⟩
  intro ψ
  have hh := patch_adjoint_equation_of_frozen_drift_equation Ω V hV X hX T f heq ψ
  rw [adjointTest_zero_eq_driftTransposeTest, ← frozen_drift_transpose_test_eq] at hh
  exact hh

end RothschildStein.H3

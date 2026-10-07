-- Copyright (c) 2026 Scott Armstrong and Amélie Loher. All rights reserved.
-- Released under Apache 2.0 license as described in the file LICENSE.
module

public import RothschildStein.H3.WeakOperatorDistributionUniqueness
public import RothschildStein.Definitions.hasDistributionEquationWithDrift
public import RothschildStein.S.Transposes

set_option autoImplicit false
set_option relaxedAutoImplicit false
@[expose] public section
noncomputable section
open Set MeasureTheory TopologicalSpace
open scoped ENNReal BigOperators
namespace RothschildStein.H3

/-- The fixed drift transpose test is the shared H3
transpose test, including both nested horizontal transposes. -/
theorem frozen_drift_transpose_test_eq {N q : ℕ}
    (U : Opens (Fin N → ℝ))
    (X : Fin (q + 1) → (Fin N → ℝ) → (Fin N → ℝ))
    (hX : ∀ i, ContDiffOn ℝ (⊤ : ℕ∞) (X i) (U : Set (Fin N → ℝ)))
    (φ : TestFunction U ℝ (⊤ : ℕ∞)) :
    sumSquaresWithDriftTransposeTest U X hX φ = driftTransposeTest U X hX φ := by
  ext x
  rw [driftTransposeTest_apply]
  simp [sumSquaresWithDriftTransposeTest, S.fieldTransposeTest_apply,
    S.fieldTransposeTest_coe, sumSquaresWithDriftTranspose]

/-- An actual fixed distribution equation identifies
the selected weak drift source almost everywhere on the local domain. -/
theorem WeakDriftOperatorData.operator_ae_eq_of_frozen_equation {N q : ℕ}
    {X : Fin (q + 1) → (Fin N → ℝ) → (Fin N → ℝ)}
    {U : Opens (Fin N → ℝ)} {p : ℝ≥0∞} {u : (Fin N → ℝ) → ℝ}
    (D : WeakDriftOperatorData X U p u) (hp : 1 ≤ p)
    (hX : ∀ i, ContDiffOn ℝ (⊤ : ℕ∞) (X i) (U : Set (Fin N → ℝ)))
    (f : (Fin N → ℝ) → ℝ)
    (heq : hasDistributionEquationWithDrift U X hX
      (Distribution.ofFun U u volume (⊤ : ℕ∞)) f) :
    D.operator =ᵐ[volume.restrict (U : Set (Fin N → ℝ))] f := by
  apply D.operator_ae_eq_of_distribution_equation hp hX f heq.1
  intro φ
  rw [adjointTest_zero_eq_driftTransposeTest, ← frozen_drift_transpose_test_eq]
  exact heq.2 φ

end RothschildStein.H3

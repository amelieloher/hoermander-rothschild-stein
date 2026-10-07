-- Copyright (c) 2026 Scott Armstrong and Amélie Loher. All rights reserved.
-- Released under Apache 2.0 license as described in the file LICENSE.
module

public import RothschildStein.H3.ZeroFieldIntrinsic
public import RothschildStein.S.Transposes
public import RothschildStein.Definitions.hasDistributionEquation
public import RothschildStein.Definitions.hasDistributionEquationWithDrift

set_option autoImplicit false
set_option relaxedAutoImplicit false
@[expose] public section
noncomputable section
open Set TopologicalSpace
open scoped BigOperators
namespace RothschildStein.H3

/-- The test-function transpose of the zero channel vanishes literally. -/
theorem fieldTransposeTest_zero_field {N : ℕ} (U : Opens (Fin N → ℝ))
    (h : ContDiffOn ℝ (⊤ : ℕ∞) (0 : (Fin N → ℝ) → (Fin N → ℝ)) (U : Set (Fin N → ℝ)))
    (φ : TestFunction U ℝ (⊤ : ℕ∞)) : fieldTransposeTest U 0 h φ = 0 := by
  ext x
  rw [S.fieldTransposeTest_apply, fieldTranspose_zero_field]
  rfl

/-- Adding the zero drift channel leaves the exact fixed test
transpose unchanged, independently of the smoothness proof witnesses. -/
theorem sumSquaresTransposeTest_zero_drift {N q : ℕ}
    (U : Opens (Fin N → ℝ)) (X : Fin q → (Fin N → ℝ) → (Fin N → ℝ))
    (hX : ∀ i, ContDiffOn ℝ (⊤ : ℕ∞) (X i) (U : Set (Fin N → ℝ)))
    (hZ : ∀ i, ContDiffOn ℝ (⊤ : ℕ∞) (Fin.cases 0 X i) (U : Set (Fin N → ℝ)))
    (φ : TestFunction U ℝ (⊤ : ℕ∞)) :
    sumSquaresWithDriftTransposeTest U (Fin.cases 0 X) hZ φ =
      sumSquaresTransposeTest U X hX φ := by
  simp only [sumSquaresWithDriftTransposeTest, sumSquaresTransposeTest,
    Fin.cases_zero, Fin.cases_succ, fieldTransposeTest_zero_field, zero_add]

/-- The two fixed distributional equations coincide after the zero
drift channel is added. This preserves the equation for arbitrary
distributions, rather than just pointwise smooth inputs. -/
theorem distributionEquation_zero_drift_iff {N q : ℕ}
    (U : Opens (Fin N → ℝ)) (X : Fin q → (Fin N → ℝ) → (Fin N → ℝ))
    (hX : ∀ i, ContDiffOn ℝ (⊤ : ℕ∞) (X i) (U : Set (Fin N → ℝ)))
    (hZ : ∀ i, ContDiffOn ℝ (⊤ : ℕ∞) (Fin.cases 0 X i) (U : Set (Fin N → ℝ)))
    (T : Distribution U ℝ (⊤ : ℕ∞)) (f : (Fin N → ℝ) → ℝ) :
    hasDistributionEquationWithDrift U (Fin.cases 0 X) hZ T f ↔
      hasDistributionEquation U X hX T f := by
  simp only [hasDistributionEquationWithDrift, hasDistributionEquation,
    sumSquaresTransposeTest_zero_drift U X hX hZ]

end RothschildStein.H3

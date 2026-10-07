-- Copyright (c) 2026 Scott Armstrong and Amélie Loher. All rights reserved.
-- Released under Apache 2.0 license as described in the file LICENSE.
module

public import RothschildStein.H3.FrozenDriftEquationBridge

set_option autoImplicit false
set_option relaxedAutoImplicit false
@[expose] public section
noncomputable section
open Set MeasureTheory TopologicalSpace
open scoped ENNReal
namespace RothschildStein.H3

/-- The fixed equation for an actual locally integrable input
restricts to every smaller open domain, with the same forcing function. -/
theorem frozen_drift_equation_restrict {N q : ℕ}
    (R U : Opens (Fin N → ℝ)) (hUR : (U : Set (Fin N → ℝ)) ⊆ R)
    (X : Fin (q + 1) → (Fin N → ℝ) → (Fin N → ℝ))
    (hX : ∀ i, ContDiffOn ℝ (⊤ : ℕ∞) (X i) (R : Set (Fin N → ℝ)))
    (u f : (Fin N → ℝ) → ℝ)
    (hu : LocallyIntegrableOn u (R : Set (Fin N → ℝ)) volume)
    (heq : hasDistributionEquationWithDrift R X hX
      (Distribution.ofFun R u volume (⊤ : ℕ∞)) f) :
    hasDistributionEquationWithDrift U X (fun i => (hX i).mono hUR)
      (Distribution.ofFun U u volume (⊤ : ℕ∞)) f := by
  refine ⟨heq.1.mono_set hUR, ?_⟩
  intro φ
  let φR : TestFunction R ℝ (⊤ : ℕ∞) :=
    ⟨φ, φ.contDiff, φ.hasCompactSupport, φ.tsupport_subset.trans hUR⟩
  have hcU : (sumSquaresWithDriftTransposeTest U X (fun i => (hX i).mono hUR) φ :
      (Fin N → ℝ) → ℝ) = sumSquaresWithDriftTranspose X φ := by
    rw [frozen_drift_transpose_test_eq]
    funext x
    exact driftTransposeTest_apply U X (fun i => (hX i).mono hUR) φ x
  have hcR : (sumSquaresWithDriftTransposeTest R X hX φR :
      (Fin N → ℝ) → ℝ) = sumSquaresWithDriftTranspose X φR := by
    rw [frozen_drift_transpose_test_eq]
    funext x
    exact driftTransposeTest_apply R X hX φR x
  have hφR : (φR : (Fin N → ℝ) → ℝ) = (φ : (Fin N → ℝ) → ℝ) := rfl
  have hh := heq.2 φR
  rw [Distribution.ofFun_apply hu, Distribution.ofFun_apply heq.1] at hh
  rw [Distribution.ofFun_apply (hu.mono_set hUR),
    Distribution.ofFun_apply (heq.1.mono_set hUR)]
  simpa only [hcU, hcR, hφR] using hh

end RothschildStein.H3

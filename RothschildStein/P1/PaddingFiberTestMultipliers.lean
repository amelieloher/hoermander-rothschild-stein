-- Copyright (c) 2026 Scott Armstrong and Amélie Loher. All rights reserved.
-- Released under Apache 2.0 license as described in the file LICENSE.
module

public import RothschildStein.P1.PaddingFiberTestContinuity
public import RothschildStein.Definitions.testMultiplierOn
public import Mathlib.Analysis.Calculus.ContDiff.Comp

set_option autoImplicit false
set_option relaxedAutoImplicit false
@[expose] public section
noncomputable section
open Set MeasureTheory TopologicalSpace
namespace RothschildStein.P1

/-- A locally smooth base coefficient pulls back smoothly to
any padded domain projecting into the original open set. -/
theorem contDiffOn_paddingBaseCoefficient {n d : ℕ}
    (Ω : Opens (Fin n → ℝ)) (U : Opens (Fin (n + d) → ℝ))
    (hU : (U : Set (Fin (n + d) → ℝ)) ⊆ basePoint ⁻¹' (Ω : Set (Fin n → ℝ)))
    (a : (Fin n → ℝ) → ℝ) (ha : ContDiffOn ℝ (⊤ : ℕ∞) a (Ω : Set (Fin n → ℝ))) :
    ContDiffOn ℝ (⊤ : ℕ∞) (fun ξ => a (basePoint ξ)) (U : Set (Fin (n + d) → ℝ)) :=
  ha.comp (paddingBaseCLM n d).contDiff.contDiffOn hU

/-- Multiplication by a base coefficient commutes with LF
fiber integration, with only local smoothness on the original domain. -/
theorem paddingFiberTestCLM_multiplier_base {n d : ℕ}
    (Ω : Opens (Fin n → ℝ)) (U : Opens (Fin (n + d) → ℝ))
    (hU : (U : Set (Fin (n + d) → ℝ)) ⊆ basePoint ⁻¹' (Ω : Set (Fin n → ℝ)))
    (a : (Fin n → ℝ) → ℝ) (ha : ContDiffOn ℝ (⊤ : ℕ∞) a (Ω : Set (Fin n → ℝ)))
    (φ : _root_.TestFunction U ℝ ⊤) :
    paddingFiberTestCLM Ω U hU
      (testMultiplierOn U (fun ξ => a (basePoint ξ))
        (contDiffOn_paddingBaseCoefficient Ω U hU a ha) φ) =
      testMultiplierOn Ω a ha (paddingFiberTestCLM Ω U hU φ) := by
  ext x
  rw [paddingFiberTestCLM_apply]
  change (∫ z : Fin d → ℝ, φ (joinPoint x z) * a (basePoint (joinPoint x z))) =
    paddingFiberTestCLM Ω U hU φ x * a x
  rw [paddingFiberTestCLM_apply]
  simp_rw [← paddingBaseCLM_apply n d, paddingBaseCLM_join]
  exact integral_mul_const _ _

end RothschildStein.P1

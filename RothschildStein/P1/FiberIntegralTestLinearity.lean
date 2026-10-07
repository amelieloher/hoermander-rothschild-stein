-- Copyright (c) 2026 Scott Armstrong and Amélie Loher. All rights reserved.
-- Released under Apache 2.0 license as described in the file LICENSE.
module

public import RothschildStein.P1.FiberIntegralTestDefs

set_option autoImplicit false
set_option relaxedAutoImplicit false
@[expose] public section
noncomputable section
open Set MeasureTheory TopologicalSpace
namespace RothschildStein.P1

/-- Fiber integration of actual tests is additive. -/
theorem fiberIntegralTest_add {n d : ℕ} {B : Type*}
    [NormedAddCommGroup B] [NormedSpace ℝ B] [CompleteSpace B]
    (Ω : Opens (Fin n → ℝ))
    (U : Opens ((Fin n → ℝ) × (Fin d → ℝ)))
    (hU : (U : Set ((Fin n → ℝ) × (Fin d → ℝ))) ⊆ Prod.fst ⁻¹' (Ω : Set (Fin n → ℝ)))
    (φ ψ : _root_.TestFunction U B ⊤) :
    fiberIntegralTest Ω U hU (φ + ψ) =
      fiberIntegralTest Ω U hU φ + fiberIntegralTest Ω U hU ψ := by
  ext x
  change (∫ z, φ (x, z) + ψ (x, z)) = (∫ z, φ (x, z)) + ∫ z, ψ (x, z)
  exact integral_add (integrable_fiberSection φ.continuous φ.hasCompactSupport x)
    (integrable_fiberSection ψ.continuous ψ.hasCompactSupport x)

/-- Fiber integration of actual tests is real linear. -/
theorem fiberIntegralTest_smul {n d : ℕ} {B : Type*}
    [NormedAddCommGroup B] [NormedSpace ℝ B] [CompleteSpace B]
    (Ω : Opens (Fin n → ℝ))
    (U : Opens ((Fin n → ℝ) × (Fin d → ℝ)))
    (hU : (U : Set ((Fin n → ℝ) × (Fin d → ℝ))) ⊆ Prod.fst ⁻¹' (Ω : Set (Fin n → ℝ)))
    (c : ℝ) (φ : _root_.TestFunction U B ⊤) :
    fiberIntegralTest Ω U hU (c • φ) = c • fiberIntegralTest Ω U hU φ := by
  ext x
  change (∫ z, c • φ (x, z)) = c • ∫ z, φ (x, z)
  exact integral_smul c (fun z => φ (x, z))

end RothschildStein.P1

-- Copyright (c) 2026 Scott Armstrong and Amélie Loher. All rights reserved.
-- Released under Apache 2.0 license as described in the file LICENSE.
module

public import RothschildStein.P1.FiberIntegralSmoothness
public import Mathlib.Analysis.Distribution.TestFunction

set_option autoImplicit false
set_option relaxedAutoImplicit false
@[expose] public section
noncomputable section
open Set MeasureTheory TopologicalSpace
namespace RothschildStein.P1

/-- The actual base test obtained by integrating a smooth
compactly supported test over the added-coordinate fiber. -/
def fiberIntegralTest {n d : ℕ} {B : Type*}
    [NormedAddCommGroup B] [NormedSpace ℝ B] [CompleteSpace B]
    (Ω : Opens (Fin n → ℝ))
    (U : Opens ((Fin n → ℝ) × (Fin d → ℝ)))
    (hU : (U : Set ((Fin n → ℝ) × (Fin d → ℝ))) ⊆ Prod.fst ⁻¹' (Ω : Set (Fin n → ℝ)))
    (φ : _root_.TestFunction U B ⊤) : _root_.TestFunction Ω B ⊤ where
  toFun x := ∫ z, φ (x, z)
  contDiff' := contDiff_fiberIntegral φ.contDiff φ.hasCompactSupport
  hasCompactSupport' := hasCompactSupport_fiberIntegral φ.hasCompactSupport
  tsupport_subset' := by
    intro x hx
    obtain ⟨p, hp, rfl⟩ := tsupport_fiberIntegral_subset φ.hasCompactSupport hx
    exact hU (φ.tsupport_subset hp)

end RothschildStein.P1

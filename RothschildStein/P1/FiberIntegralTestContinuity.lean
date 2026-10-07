-- Copyright (c) 2026 Scott Armstrong and Amélie Loher. All rights reserved.
-- Released under Apache 2.0 license as described in the file LICENSE.
module

public import RothschildStein.P1.FiberIntegralSupportedContinuity
public import RothschildStein.P1.FiberIntegralTestLinearity

set_option autoImplicit false
set_option relaxedAutoImplicit false
@[expose] public section
noncomputable section
open Set MeasureTheory TopologicalSpace
namespace RothschildStein.P1

/-- Fiber integration is continuous for the actual LF topology
on test functions. This is the map needed for tensoring a distribution
with the constant distribution on the added coordinates. -/
def fiberIntegralTestCLM {n d : ℕ} {B : Type*}
    [NormedAddCommGroup B] [NormedSpace ℝ B] [CompleteSpace B]
    (Ω : Opens (Fin n → ℝ))
    (U : Opens ((Fin n → ℝ) × (Fin d → ℝ)))
    (hU : (U : Set ((Fin n → ℝ) × (Fin d → ℝ))) ⊆
      Prod.fst ⁻¹' (Ω : Set (Fin n → ℝ))) :
    _root_.TestFunction U B ⊤ →L[ℝ] _root_.TestFunction Ω B ⊤ :=
  _root_.TestFunction.mkCLM ℝ (fiberIntegralTest Ω U hU)
    (fiberIntegralTest_add Ω U hU) (fiberIntegralTest_smul Ω U hU) (by
      intro K hK
      have hbase : (K.map Prod.fst continuous_fst : Set (Fin n → ℝ)) ⊆ Ω := by
        intro x hx
        obtain ⟨p, hp, rfl⟩ := hx
        exact hU (hK hp)
      let T := (_root_.TestFunction.ofSupportedInCLM ℝ hbase).comp
        (fiberIntegralSupportedCLM (B := B) K)
      convert T.continuous using 1
      funext φ
      ext x
      rfl)

end RothschildStein.P1

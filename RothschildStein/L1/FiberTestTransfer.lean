-- Copyright (c) 2026 Scott Armstrong and Amélie Loher. All rights reserved.
-- Released under Apache 2.0 license as described in the file LICENSE.
module

public import RothschildStein.P1.PaddingFiberTestTranspose
public import RothschildStein.P1.PaddingDistributionTensorDefs
public import RothschildStein.Definitions.triangularLift

set_option autoImplicit false
set_option relaxedAutoImplicit false
@[expose] public section
noncomputable section
open Set MeasureTheory TopologicalSpace
open scoped BigOperators
namespace RothschildStein.L1
open RothschildStein.P1

/-- The actual continuous fiber integration map (BB p. 608, (11.101)). -/
abbrev fiberTestCLM {n m : ℕ} (Ω : Opens (Fin n → ℝ))
    (U : Opens (Fin (n + m) → ℝ))
    (hU : (U : Set (Fin (n + m) → ℝ)) ⊆ basePoint ⁻¹' (Ω : Set (Fin n → ℝ))) :=
  paddingFiberTestCLM (B := ℝ) Ω U hU

end RothschildStein.L1

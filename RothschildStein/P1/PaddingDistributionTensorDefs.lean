-- Copyright (c) 2026 Scott Armstrong and Amélie Loher. All rights reserved.
-- Released under Apache 2.0 license as described in the file LICENSE.
module

public import RothschildStein.P1.PaddingFiberTestContinuity
public import Mathlib.Analysis.Distribution.Distribution

set_option autoImplicit false
set_option relaxedAutoImplicit false
@[expose] public section
noncomputable section
open Set MeasureTheory TopologicalSpace
namespace RothschildStein.P1

/-- The arbitrary-distribution tensor with one on the
joined-coordinate domain. It is continuous on actual distribution spaces
and imposes no function-representative premise. -/
def paddingDistributionTensorOneCLM {n d : ℕ} {B : Type*}
    [NormedAddCommGroup B] [NormedSpace ℝ B]
    (Ω : Opens (Fin n → ℝ)) (U : Opens (Fin (n + d) → ℝ))
    (hU : (U : Set (Fin (n + d) → ℝ)) ⊆ basePoint ⁻¹' (Ω : Set (Fin n → ℝ))) :
    _root_.Distribution Ω B ⊤ →L[ℝ] _root_.Distribution U B ⊤ :=
  (paddingFiberTestCLM (B := ℝ) Ω U hU).precompCompactConvergenceCLM B

/-- The tensor pairing is exactly the original distribution
applied to the actual fiber-integrated test. -/
theorem paddingDistributionTensorOneCLM_apply {n d : ℕ} {B : Type*}
    [NormedAddCommGroup B] [NormedSpace ℝ B]
    (Ω : Opens (Fin n → ℝ)) (U : Opens (Fin (n + d) → ℝ))
    (hU : (U : Set (Fin (n + d) → ℝ)) ⊆ basePoint ⁻¹' (Ω : Set (Fin n → ℝ)))
    (T : _root_.Distribution Ω B ⊤) (φ : _root_.TestFunction U ℝ ⊤) :
    paddingDistributionTensorOneCLM Ω U hU T φ = T (paddingFiberTestCLM Ω U hU φ) := rfl

end RothschildStein.P1

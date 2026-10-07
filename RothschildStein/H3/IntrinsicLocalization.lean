-- Copyright (c) 2026 Scott Armstrong and Amélie Loher. All rights reserved.
-- Released under Apache 2.0 license as described in the file LICENSE.
module

public import RothschildStein.S.IntrinsicUniqueness
public import RothschildStein.S.IntrinsicCurveExistence
public import RothschildStein.S.ClassicalWords

set_option autoImplicit false
set_option relaxedAutoImplicit false
set_option backward.isDefEq.respectTransparency false
@[expose] public section
noncomputable section
namespace RothschildStein.H3
open Set Filter TopologicalSpace
open scoped Topology

/-- Smooth scalar functions have the fixed intrinsic derivative along
 each locally smooth field. -/
theorem intrinsicDeriv_of_differentiable {n : ℕ} (Ω : Opens (Fin n → ℝ))
    (X : (Fin n → ℝ) → (Fin n → ℝ))
    (hX : ContDiffOn ℝ (⊤ : ℕ∞) X (Ω : Set (Fin n → ℝ)))
    {f : (Fin n → ℝ) → ℝ} (hf : Differentiable ℝ f) :
    hasIntrinsicDeriv Ω X f (fieldDerivative X f) := by
  intro x hx
  refine ⟨RothschildStein.S.exists_intrinsic_integral_curve Ω X hX hx,
    fun γ hzero hγ _ => ?_⟩
  have hc := (hf (γ 0)).hasFDerivAt.comp_hasDerivAt 0 hγ.self_of_nhds
  simpa only [Function.comp_def, fieldDerivative, hzero] using hc

end RothschildStein.H3

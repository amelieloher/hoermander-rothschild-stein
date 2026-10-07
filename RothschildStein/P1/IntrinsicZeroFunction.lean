-- Copyright (c) 2026 Scott Armstrong and Amélie Loher. All rights reserved.
-- Released under Apache 2.0 license as described in the file LICENSE.
module

public import RothschildStein.S.IntrinsicCurveExistence
public import RothschildStein.Definitions.hasIntrinsicWordDeriv

set_option autoImplicit false
set_option relaxedAutoImplicit false
@[expose] public section
noncomputable section
open Set Filter TopologicalSpace
namespace RothschildStein.P1

/-- The zero function has zero intrinsic derivative along
any locally smooth field, with the required integral-curve certificate. -/
theorem hasIntrinsicDeriv_zero_function {n : ℕ}
    (Ω : Opens (Fin n → ℝ)) (X : (Fin n → ℝ) → (Fin n → ℝ))
    (hX : ContDiffOn ℝ (⊤ : ℕ∞) X (Ω : Set (Fin n → ℝ))) :
    hasIntrinsicDeriv Ω X (fun _ => 0) (fun _ => 0) := by
  intro x hx
  refine ⟨S.exists_intrinsic_integral_curve Ω X hX hx, ?_⟩
  intro γ _ _ _
  exact hasDerivAt_const 0 (0 : ℝ)

end RothschildStein.P1

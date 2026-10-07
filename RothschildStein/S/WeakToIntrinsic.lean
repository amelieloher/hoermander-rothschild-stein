-- Copyright (c) 2026 Scott Armstrong and Amélie Loher. All rights reserved.
-- Released under Apache 2.0 license as described in the file LICENSE.
module

public import RothschildStein.S.WeakCurveDerivative
public import RothschildStein.S.IntrinsicCurveExistence

set_option autoImplicit false
set_option relaxedAutoImplicit false
@[expose] public section
noncomputable section
open Set TopologicalSpace
namespace RothschildStein.S
variable {n : ℕ}

/-- A continuous weak field derivative is the exact intrinsic derivative, including existence and the derivative along
all local integral curves. No bracket condition or drift restriction
is used (BB Thm 2.20, p. 86; converse to Prop 2.22). -/
theorem hasIntrinsicDeriv_of_continuous_weak_derivative
    (Ω : Opens (Fin n → ℝ)) (X : (Fin n → ℝ) → (Fin n → ℝ))
    (hX : ContDiffOn ℝ (⊤ : ℕ∞) X (Ω : Set (Fin n → ℝ)))
    (f g : (Fin n → ℝ) → ℝ)
    (hf : ContinuousOn f (Ω : Set (Fin n → ℝ)))
    (hg : ContinuousOn g (Ω : Set (Fin n → ℝ)))
    (hw : hasWeakWordDeriv (fun _ : Fin 1 => X) Ω [0] f g) :
    hasIntrinsicDeriv Ω X f g := by
  intro x hx
  refine ⟨exists_intrinsic_integral_curve Ω X hX hx,fun γ hzero hγ _ => ?_⟩
  have hmem : γ 0 ∈ (Ω : Set (Fin n → ℝ)) := hzero ▸ hx
  simpa only [hzero] using hasDerivAt_comp_curve_of_continuous_weak_derivative
    Ω X hX f g hf hg hw γ hγ hmem

end RothschildStein.S

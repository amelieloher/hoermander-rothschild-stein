-- Copyright (c) 2026 Scott Armstrong and Amélie Loher. All rights reserved.
-- Released under Apache 2.0 license as described in the file LICENSE.
module

public import RothschildStein.P1.RegularKernelWeakDerivative

set_option autoImplicit false
set_option relaxedAutoImplicit false
@[expose] public section
noncomputable section
open Set MeasureTheory
namespace RothschildStein.P1
variable {N k : ℕ} {F : KernelFrame N}

/-- The actual regular-kernel weak derivative for any selected
letter of the full lifted alphabet, including the drift letter. -/
theorem regularKernel_action_hasWeakWordDeriv
    {r : (Fin N → ℝ) → (Fin N → ℝ) → ℝ} (hr : IsRegularKernel F 1 r)
    (X : Fin k → (Fin N → ℝ) → (Fin N → ℝ)) (i : Fin k)
    (hX : ContDiffOn ℝ (⊤ : ℕ∞) (X i) (F.V : Set (Fin N → ℝ)))
    (ψ : TestFunction F.V ℝ (⊤ : ℕ∞)) :
    hasWeakWordDeriv X F.V [i] (fun ξ => ∫ η, r ξ η * ψ η)
      (fun ξ => ∫ η, fieldDerivative (X i) (fun x => r x η) ξ * ψ η) := by
  simpa only [hasWeakWordDeriv, wordTranspose] using
    regularKernel_action_hasWeakFieldDeriv hr (fun _ : Fin 1 => X i) (fun _ => hX) ψ

end RothschildStein.P1

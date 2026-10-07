-- Copyright (c) 2026 Scott Armstrong and Amélie Loher. All rights reserved.
-- Released under Apache 2.0 license as described in the file LICENSE.
module

public import RothschildStein.Definitions.hasIntrinsicWordDeriv

set_option autoImplicit false
set_option relaxedAutoImplicit false
@[expose] public section
noncomputable section
open Set TopologicalSpace
namespace RothschildStein.P1

/-- Iterated intrinsic derivatives depend only on the input
function on the open domain, including the pointwise empty word. -/
theorem hasIntrinsicWordDeriv_congr_input {n q : ℕ}
    (Ω : Opens (Fin n → ℝ)) (X : Fin q → (Fin n → ℝ) → (Fin n → ℝ))
    (I : List (Fin q)) {f h g : (Fin n → ℝ) → ℝ}
    (he : EqOn f h (Ω : Set (Fin n → ℝ)))
    (hg : hasIntrinsicWordDeriv X Ω I f g) : hasIntrinsicWordDeriv X Ω I h g := by
  induction I generalizing g with
  | nil => exact hg.trans he
  | cons i I ih =>
    obtain ⟨a, ha, hga⟩ := hg
    exact ⟨a, ih ha, hga⟩

end RothschildStein.P1

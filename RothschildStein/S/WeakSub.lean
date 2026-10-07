-- Copyright (c) 2026 Scott Armstrong and Amélie Loher. All rights reserved.
-- Released under Apache 2.0 license as described in the file LICENSE.
module

public import RothschildStein.S.WeakDeriv

set_option autoImplicit false
set_option relaxedAutoImplicit false
@[expose] public section
noncomputable section
open Set MeasureTheory TopologicalSpace Filter
open scoped BigOperators Topology
namespace RothschildStein.S
variable {n m : ℕ}

/-- Differences of weak word derivatives are derivatives of the
corresponding difference (BB Def. 2.1, pp. 67–68). -/
theorem hasWeakWordDeriv_sub
    (X : Fin m → (Fin n → ℝ) → (Fin n → ℝ)) (Ω : Opens (Fin n → ℝ))
    (hX : ∀ i, ContDiffOn ℝ (⊤ : ℕ∞) (X i) (Ω : Set (Fin n → ℝ)))
    {I : List (Fin m)} {f g h k : (Fin n → ℝ) → ℝ}
    (hf : hasWeakWordDeriv X Ω I f g) (hh : hasWeakWordDeriv X Ω I h k) :
    hasWeakWordDeriv X Ω I (fun x => f x - h x) (fun x => g x - k x) := by
  have hn := hasWeakWordDeriv_smul X Ω hh (-1)
  have hs := hasWeakWordDeriv_add X Ω hX hf hn
  convert hs using 1 <;> (funext x; ring)

end RothschildStein.S

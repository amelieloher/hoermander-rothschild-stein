-- Copyright (c) 2026 Scott Armstrong and Amélie Loher. All rights reserved.
-- Released under Apache 2.0 license as described in the file LICENSE.
module
public import RothschildStein.L1.OneVariableLift
public import RothschildStein.S.ClassicalWords
public import RothschildStein.P1.BracketExpansion
@[expose] public section
set_option autoImplicit false
set_option relaxedAutoImplicit false
noncomputable section
open Set TopologicalSpace Filter
open scoped Topology
namespace RothschildStein.L1

/-- Every ordered lifted product acting on a base-dependent smooth
function is the pullback of the original product (BB (10.6)). -/
theorem oneVariableLift_wordDerivative_pullback {a n : ℕ}
    (Ω : Opens (Fin n → ℝ))
    (X : Fin a → (Fin n → ℝ) → (Fin n → ℝ))
    (hX : ∀ i, ContDiffOn ℝ (⊤ : ℕ∞) (X i) Ω)
    (u : Fin a → (Fin n → ℝ) → ℝ) (I : List (Fin a))
    (f : (Fin n → ℝ) → ℝ) (hf : ContDiffOn ℝ (⊤ : ℕ∞) f Ω) :
    EqOn (wordDerivative (oneVariableLift X u) I (f ∘ P1.paddingBaseCLM n 1))
      ((wordDerivative X I f) ∘ P1.paddingBaseCLM n 1)
      ((P1.paddingBaseCLM n 1) ⁻¹' (Ω : Set (Fin n → ℝ))) := by
  induction I with
  | nil => intro ξ hξ; rfl
  | cons i I ih =>
    intro ξ hξ
    have ho : IsOpen ((P1.paddingBaseCLM n 1) ⁻¹' (Ω : Set (Fin n → ℝ))) :=
      Ω.isOpen.preimage (P1.paddingBaseCLM n 1).continuous
    have he := ih.eventuallyEq_of_mem (ho.mem_nhds hξ)
    change fderiv ℝ _ ξ _ = _
    rw [he.fderiv_eq]
    exact oneVariableLift_fieldDerivative_pullback X u i _ ξ
      (((S.contDiffOn_wordDerivative Ω X hX I f hf).contDiffAt
        (Ω.isOpen.mem_nhds hξ)).differentiableAt (by simp))

/-- A nonempty ordered product on the new coordinate is the
original prefix product on the last generator's vertical coefficient
(BB Proposition 10.17, (10.7)). -/
theorem oneVariableLift_wordDerivative_vertical {a n : ℕ}
    (Ω : Opens (Fin n → ℝ))
    (X : Fin a → (Fin n → ℝ) → (Fin n → ℝ))
    (hX : ∀ i, ContDiffOn ℝ (⊤ : ℕ∞) (X i) Ω)
    (u : Fin a → (Fin n → ℝ) → ℝ)
    (hu : ∀ i, ContDiffOn ℝ (⊤ : ℕ∞) (u i) Ω)
    (I : List (Fin a)) (j : Fin a) {ξ : Fin (n+1) → ℝ}
    (hξ : P1.paddingBaseCLM n 1 ξ ∈ Ω) :
    wordDerivative (oneVariableLift X u) (I ++ [j])
      (fun η => P1.paddingFiberCLM n 1 η 0) ξ =
      wordDerivative X I (u j) (P1.paddingBaseCLM n 1 ξ) := by
  rw [P1.wordDerivative_append]
  have he : wordDerivative (oneVariableLift X u) [j]
      (fun η => P1.paddingFiberCLM n 1 η 0) = (u j) ∘ P1.paddingBaseCLM n 1 := by
    funext η
    exact oneVariableLift_fieldDerivative_vertical X u j η
  rw [he]
  exact oneVariableLift_wordDerivative_pullback Ω X hX u I (u j) (hu j) hξ
end RothschildStein.L1

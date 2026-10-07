-- Copyright (c) 2026 Scott Armstrong and Amélie Loher. All rights reserved.
-- Released under Apache 2.0 license as described in the file LICENSE.
module
public import RothschildStein.L1.LiftedFieldSmoothness
public import RothschildStein.L1.BracketProjection
public import RothschildStein.L1.DirectFreeness
@[expose] public section
set_option autoImplicit false
set_option relaxedAutoImplicit false
noncomputable section
open Set TopologicalSpace
open scoped BigOperators
namespace RothschildStein.L1

/-- Every actual lifted commutator projects to its original
commutator on the cylinder (BB Proposition 10.17). -/
theorem oneVariableLift_wordBracket_base {a n : ℕ}
    (Ω : Opens (Fin n → ℝ))
    (X : Fin a → (Fin n → ℝ) → (Fin n → ℝ))
    (hX : ∀ i, ContDiffOn ℝ (⊤ : ℕ∞) (X i) Ω)
    (u : Fin a → (Fin n → ℝ) → ℝ)
    (hu : ∀ i, ContDiffOn ℝ (⊤ : ℕ∞) (u i) Ω) (I : List (Fin a))
    {ξ : Fin (n+1) → ℝ} (hξ : P1.paddingBaseCLM n 1 ξ ∈ Ω) :
    P1.paddingBaseCLM n 1 (wordBracket (oneVariableLift X u) I ξ) =
      wordBracket X I (P1.paddingBaseCLM n 1 ξ) :=
  wordBracket_linear_projection Ω.isOpen (oneVariableLiftDomain Ω).isOpen
    (P1.paddingBaseCLM n 1) (fun _ h => h) X (oneVariableLift X u) hX
    (oneVariableLift_contDiffOn Ω X hX u hu)
    (fun ξ _ i => oneVariableLift_base X u i ξ) I ξ hξ

/-- Adding one variable preserves every lower-order freeness
condition, because all tangent relations project to the original fields. -/
theorem oneVariableLift_freeAt_of_freeAt {a s n : ℕ} {p : Fin a → ℕ+}
    (Ω : Opens (Fin n → ℝ))
    (X : Fin a → (Fin n → ℝ) → (Fin n → ℝ))
    (hX : ∀ i, ContDiffOn ℝ (⊤ : ℕ∞) (X i) Ω)
    (u : Fin a → (Fin n → ℝ) → ℝ)
    (hu : ∀ i, ContDiffOn ℝ (⊤ : ℕ∞) (u i) Ω)
    {ξ : Fin (n+1) → ℝ} (hξ : P1.paddingBaseCLM n 1 ξ ∈ Ω)
    (hf : FreeAt p s X (P1.paddingBaseCLM n 1 ξ)) :
    FreeAt p s (oneVariableLift X u) ξ := by
  intro c
  constructor
  · intro hz
    apply (hf c).mp
    have he := congrArg (P1.paddingBaseCLM n 1) hz
    simpa only [map_sum,map_smul,oneVariableLift_wordBracket_base Ω X hX u hu _ hξ,
      map_zero] using he
  · intro hrel
    rw [← directPointEvaluation_formalWordCoefficients (oneVariableLiftDomain Ω)
      (oneVariableLift X u) (oneVariableLift_contDiffOn Ω X hX u hu) c hξ]
    rw [(formalWordCoefficientMap_eq_zero_iff c).mpr hrel,map_zero]
end RothschildStein.L1

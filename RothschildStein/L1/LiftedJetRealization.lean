-- Copyright (c) 2026 Scott Armstrong and Amélie Loher. All rights reserved.
-- Released under Apache 2.0 license as described in the file LICENSE.
module
public import RothschildStein.L1.LiftingJetCoefficients
public import RothschildStein.L1.LiftedOrderedWords
public import RothschildStein.L1.LiftedFieldSmoothness
@[expose] public section
set_option autoImplicit false
set_option relaxedAutoImplicit false
noncomputable section
open Set TopologicalSpace
namespace RothschildStein.L1

/-- The polynomial vertical coefficients realize
all bounded ordered jets of the new coordinate on the actual lift
(BB Proposition 10.17, (10.6)–(10.8)). -/
theorem exists_lift_with_vertical_word_jets {a σ n : ℕ} {p : Fin a → ℕ+}
    (Ω : Opens (Fin n → ℝ))
    (X : Fin a → (Fin n → ℝ) → (Fin n → ℝ))
    (hX : ∀ i, ContDiffOn ℝ (⊤ : ℕ∞) (X i) Ω)
    (hzero : (0 : Fin n → ℝ) ∈ Ω) (hf : FreeAt p (σ-1) X 0)
    (c : List (Fin a) → ℝ) (hc : c [] = 0) :
    ∃ U : Fin a → MvPolynomial (Fin n) ℝ,
      (∀ i, ContDiffOn ℝ (⊤ : ℕ∞)
        (oneVariableLift X (fun j x => MvPolynomial.eval x (U j)) i)
        (oneVariableLiftDomain Ω)) ∧
      ∀ I : List (Fin a), wordWeight p I ≤ σ →
        wordDerivative (oneVariableLift X (fun j x => MvPolynomial.eval x (U j))) I
          (fun η => P1.paddingFiberCLM n 1 η 0) 0 = c I := by
  classical
  obtain ⟨U,hU,hjets⟩ := exists_polynomial_lifting_coefficients Ω X hX hzero hf c
  refine ⟨U,fun i => oneVariableLift_contDiffOn Ω X hX _
    (fun j => (hU j).contDiffOn) i,?_⟩
  intro I
  induction I using List.reverseRecOn with
  | nil =>
    intro _
    simpa only [wordDerivative,map_zero,Pi.zero_apply] using hc.symm
  | append_singleton I j ih =>
    intro hw
    have hp : 1 ≤ (p j : ℕ) := (p j).pos
    have hweight : wordWeight p I + (p j : ℕ) ≤ σ := by
      simpa [wordWeight,List.map_append,List.sum_append] using hw
    have hprefix : wordWeight p I ≤ σ-1 := by omega
    rw [oneVariableLift_wordDerivative_vertical Ω X hX _
      (fun j => (hU j).contDiffOn) I j (by simpa using hzero)]
    simpa only [map_zero] using hjets j I hprefix
end RothschildStein.L1

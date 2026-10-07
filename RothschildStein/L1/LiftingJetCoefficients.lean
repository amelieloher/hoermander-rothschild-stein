-- Copyright (c) 2026 Scott Armstrong and Amélie Loher. All rights reserved.
-- Released under Apache 2.0 license as described in the file LICENSE.
module
public import RothschildStein.L1.OrderedJetRealization
@[expose] public section
set_option autoImplicit false
set_option relaxedAutoImplicit false
noncomputable section
open Set TopologicalSpace
namespace RothschildStein.L1

/-- Lower freeness supplies the polynomial vertical
coefficients prescribed by appending the generator to an ordered word
(BB Proposition 10.17, pp. 490–493, (10.6)–(10.8)). -/
theorem exists_polynomial_lifting_coefficients {a σ N : ℕ} {p : Fin a → ℕ+}
    (Ω : Opens (Fin N → ℝ)) (X : Fin a → (Fin N → ℝ) → (Fin N → ℝ))
    (hX : ∀ i, ContDiffOn ℝ (⊤ : ℕ∞) (X i) Ω) (hzero : (0 : Fin N → ℝ) ∈ Ω)
    (hf : FreeAt p (σ-1) X 0) (c : List (Fin a) → ℝ) :
    ∃ U : Fin a → MvPolynomial (Fin N) ℝ,
      (∀ j, ContDiff ℝ (⊤ : ℕ∞) (fun x => MvPolynomial.eval x (U j))) ∧
      ∀ j (I : List (Fin a)), wordWeight p I ≤ σ-1 →
        wordDerivative X I (fun x => MvPolynomial.eval x (U j)) 0 = c (I ++ [j]) := by
  classical
  have he : ∀ j : Fin a, ∃ u : MvPolynomial (Fin N) ℝ,
      ContDiff ℝ (⊤ : ℕ∞) (fun x => MvPolynomial.eval x u) ∧
      ∀ I : List (Fin a), wordWeight p I ≤ σ-1 →
        wordDerivative X I (fun x => MvPolynomial.eval x u) 0 = c (I ++ [j]) := by
    intro j
    exact exists_polynomial_with_ordered_word_jets Ω X hX hzero hf (fun I => c (I ++ [j]))
  choose U hU hjets using he
  exact ⟨U,hU,hjets⟩
end RothschildStein.L1

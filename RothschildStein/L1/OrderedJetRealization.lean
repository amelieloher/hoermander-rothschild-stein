-- Copyright (c) 2026 Scott Armstrong and Amélie Loher. All rights reserved.
-- Released under Apache 2.0 license as described in the file LICENSE.
module
public import RothschildStein.L1.PolynomialResidualInduction
public import RothschildStein.L1.PrimitiveResidualProducts
@[expose] public section
set_option autoImplicit false
set_option relaxedAutoImplicit false
noncomputable section
open Set TopologicalSpace
namespace RothschildStein.L1
open G3

/-- At a point free through s, every assignment of ordered word jets
through weighted degree s is realized by one actual polynomial, including the
empty word. No prescribed jet exceeds the cutoff (BB Proposition 10.16,
p. 490; proof pp. 495–498, (10.11)–(10.14)). -/
theorem exists_polynomial_with_ordered_word_jets {a s N : ℕ} {p : Fin a → ℕ+}
    (Ω : Opens (Fin N → ℝ)) (X : Fin a → (Fin N → ℝ) → (Fin N → ℝ))
    (hX : ∀ i, ContDiffOn ℝ (⊤ : ℕ∞) (X i) Ω) (hzero : (0 : Fin N → ℝ) ∈ Ω)
    (hf : FreeAt p s X 0) (c : List (Fin a) → ℝ) :
    ∃ u : MvPolynomial (Fin N) ℝ,
      ContDiff ℝ (⊤ : ℕ∞) (fun x => MvPolynomial.eval x u) ∧
      ∀ I : List (Fin a), wordWeight p I ≤ s →
        wordDerivative X I (fun x => MvPolynomial.eval x u) 0 = c I := by
  obtain ⟨u,hu,hres⟩ := exists_polynomial_vanishing_nested_residuals Ω X hX hzero hf c (s+1)
  refine ⟨u,hu,?_⟩
  intro I hI
  have hl : (I.map Nested.letter).length < s+1 := by
    have hb := length_le_weight p I
    rw [List.length_map]
    omega
  have hw : nestedResidualWeight p (I.map Nested.letter) ≤ s := by
    rw [nestedResidualWeight_letters]
    exact hI
  have hz := hres (I.map Nested.letter) hl hw
  rw [nestedResidualProduct_letters,wordJetResidual_single Ω X hX _ hzero c I] at hz
  exact (sub_eq_zero.mp hz).symm
end RothschildStein.L1

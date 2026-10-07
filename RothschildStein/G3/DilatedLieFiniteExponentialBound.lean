-- Copyright (c) 2026 Scott Armstrong and Amélie Loher. All rights reserved.
-- Released under Apache 2.0 license as described in the file LICENSE.
module
public import RothschildStein.G3.IntegralCurveFiniteExponential
public import RothschildStein.G3.DilatedExponentialEvaluation
public import RothschildStein.G3.BasisLinearInput
@[expose] public section
noncomputable section
open Set TopologicalSpace
open scoped BigOperators
namespace RothschildStein.G3

/-- The actual time-one flow of a dilated finite Lie coefficient
agrees with its finite associative exponential up to |delta|^(s+1).
Constants use finite bracket-field and test-function jets, without a
spanning hypothesis on actual fields (BB Lemma 9.22, pp. 413–414). -/
theorem dilatedLieCurve_finiteExponential_bound {a s N R : ℕ} {p : Fin a → ℕ+}
    (D : FreeModelData a s p) (Ω : Opens (Fin N → ℝ))
    (X : Fin a → (Fin N → ℝ) → (Fin N → ℝ))
    (hX : ∀ i, ContDiffOn ℝ (⊤ : ℕ∞) (X i) Ω)
    (f : formalSpan a s p) (δ : ℝ) (hδ : |δ| ≤ 1)
    {a₀ b₀ Bv Bx F : ℝ} (α : ℝ → (Fin N → ℝ))
    (hmem : ∀ t ∈ Ioo a₀ b₀, α t ∈ Ω)
    (hsegment : ∀ t ∈ Icc (0 : ℝ) 1, t ∈ Ioo a₀ b₀)
    (g : smoothOnFunctions Ω) (hn : s + 1 ≤ R) (hBx : 0 ≤ Bx)
    (hwords : ∀ t ∈ Icc (0 : ℝ) 1, ∀ j ≤ R,
      (∑ l, |D.basis.equivFun f l| *
        ‖iteratedFDeriv ℝ j (wordBracket X (modelBasisWord D l)) (α t)‖) ≤ Bv)
    (hbase : ∀ l, ∀ j ≤ s,
      ‖iteratedFDeriv ℝ j (wordBracket X (modelBasisWord D l)) (α 0)‖ ≤ Bx)
    (hgjet : ∀ t ∈ Icc (0 : ℝ) 1, ∀ j ≤ R,
      ‖iteratedFDeriv ℝ j g.val (α t)‖ ≤ F) :
    let V := finiteLieField D X
      ⟨finiteDilate δ f.val, finiteDilate_mem_formalSpan δ f.property⟩
    (∀ t ∈ Ioo a₀ b₀, HasDerivAt α (V (α t)) t) →
    ‖g.val (α 1) - (differentialWordEvaluation Ω X hX
      (finitePolynomial (finiteExp (coefficientDilationHom δ f.val))) g).val (α 0)‖ ≤
      (((2 ^ R * Bv) ^ (s + 1) * F) +
        exponentialTailCoefficientBound s s (basisAlphabetWeight D)
          (linearWordPolynomial (D.basis.equivFun f)) Bx F) * |δ| ^ (s + 1) := by
  intro V hODE
  have hV := finiteLieField_contDiffOn D Ω X hX
    ⟨finiteDilate δ f.val, finiteDilate_mem_formalSpan δ f.property⟩
  have hVjet : ∀ t ∈ Icc (0 : ℝ) 1, ∀ j ≤ R,
      ‖iteratedFDeriv ℝ j V (α t)‖ ≤ |δ| * Bv := by
    intro t ht j hj
    exact (norm_iteratedFDeriv_dilatedLieField_le D Ω X hX f δ hδ j
      (hmem t (hsegment t ht))).trans
      (mul_le_mul_of_nonneg_left (hwords t ht j hj) (abs_nonneg δ))
  have hb := integralCurve_linearInput_finiteExponential_bound (basisAlphabetWeight D) Ω
    (fun l => wordBracket X (modelBasisWord D l))
    (fun l => G1.wordBracket_contDiffOn Ω.isOpen X hX (modelBasisWord D l))
    (fun l => D.weight_bound l) δ (D.basis.equivFun f) V hV
    (dilatedLieField_eq_weighted_combination D X f δ) α hODE hmem hsegment g hn hBx
    hVjet hbase hgjet hδ
  rw [truncate_linear_basis_input] at hb
  have hx : α 0 ∈ Ω := hmem 0 (hsegment 0 (by simp))
  rw [differentialWordEvaluation_dilated_basis_exp D Ω X hX f δ g hx]
  exact hb
end RothschildStein.G3

-- Copyright (c) 2026 Scott Armstrong and Amélie Loher. All rights reserved.
-- Released under Apache 2.0 license as described in the file LICENSE.
module
public import RothschildStein.G3.TwoFlowFiniteExponentialBound
public import RothschildStein.G3.DilatedLieFiniteExponentialBound
public import RothschildStein.G3.DilatedBasisBCHExponentialEvaluation
@[expose] public section
noncomputable section
open Set TopologicalSpace
open scoped BigOperators
namespace RothschildStein.G3

/-- Two arbitrary retained Lie inputs satisfy the weighted BCH comparison,
using the bracket alphabet and finite jets of ordinary order at most 2s+1. -/
theorem generalLie_BCH_integralCurves_comparison_bound {a s N R : ℕ} {p : Fin a → ℕ+}
    (D : FreeModelData a s p) (Ω : Opens (Fin N → ℝ))
    (X : Fin a → (Fin N → ℝ) → (Fin N → ℝ))
    (hX : ∀ i, ContDiffOn ℝ (⊤ : ℕ∞) (X i) Ω)
    (f g : formalSpan a s p) (δ : ℝ)
    (U V : (Fin N → ℝ) → (Fin N → ℝ))
    (hU : ContDiffOn ℝ (⊤ : ℕ∞) U Ω) (hV : ContDiffOn ℝ (⊤ : ℕ∞) V Ω)
    (hUcomb : U = fun x => ∑ j, D.basis.equivFun f j • (δ^D.weight j • wordBracket X (modelBasisWord D j) x))
    (hVcomb : V = fun x => ∑ j, D.basis.equivFun g j • (δ^D.weight j • wordBracket X (modelBasisWord D j) x))
    {a₀ b₀ Buv Bbr Bg F : ℝ} (α β γ : ℝ → (Fin N → ℝ))
    (hα : ∀ t ∈ Ioo a₀ b₀, HasDerivAt α (U (α t)) t)
    (hβ : ∀ t ∈ Ioo a₀ b₀, HasDerivAt β (V (β t)) t)
    (hγ : ∀ t ∈ Ioo a₀ b₀, HasDerivAt γ
      (finiteLieField D X ⟨finiteDilate δ (modelProduct f g).val,
        finiteDilate_mem_formalSpan δ (modelProduct f g).property⟩ (γ t)) t)
    (hαmem : ∀ t ∈ Ioo a₀ b₀, α t ∈ Ω)
    (hβmem : ∀ t ∈ Ioo a₀ b₀, β t ∈ Ω)
    (hγmem : ∀ t ∈ Ioo a₀ b₀, γ t ∈ Ω)
    (hβ₀ : β 0 = α 1) (hγ₀ : γ 0 = α 0)
    (hseg : ∀ t ∈ Icc (0 : ℝ) 1, t ∈ Ioo a₀ b₀)
    (q : smoothOnFunctions Ω) (hs : 2*s+1 ≤ R)
    (hBuv : 0 ≤ Buv) (hBbr : 0 ≤ Bbr) (hδ : |δ| ≤ 1)
    (hUjet : ∀ t ∈ Icc (0 : ℝ) 1, ∀ j ≤ R, ‖iteratedFDeriv ℝ j U (α t)‖ ≤ |δ| * Buv)
    (hVαjet : ∀ t ∈ Icc (0 : ℝ) 1, ∀ j ≤ R, ‖iteratedFDeriv ℝ j V (α t)‖ ≤ |δ| * Buv)
    (hVβjet : ∀ t ∈ Icc (0 : ℝ) 1, ∀ j ≤ R, ‖iteratedFDeriv ℝ j V (β t)‖ ≤ |δ| * Buv)
    (hbase : ∀ j k, k ≤ 2*s → ‖iteratedFDeriv ℝ k (wordBracket X (modelBasisWord D j)) (α 0)‖ ≤ Bbr)
    (hqαjet : ∀ t ∈ Icc (0 : ℝ) 1, ∀ j ≤ R, ‖iteratedFDeriv ℝ j q.val (α t)‖ ≤ F)
    (hqβjet : ∀ t ∈ Icc (0 : ℝ) 1, ∀ j ≤ R, ‖iteratedFDeriv ℝ j q.val (β t)‖ ≤ F)
    (hwords : ∀ t ∈ Icc (0 : ℝ) 1, ∀ j ≤ s+1,
      (∑ l, |D.basis.equivFun (modelProduct f g) l| * 
        ‖iteratedFDeriv ℝ j (wordBracket X (modelBasisWord D l)) (γ t)‖) ≤ Bg)
    (hqγjet : ∀ t ∈ Icc (0 : ℝ) 1, ∀ j ≤ s+1, ‖iteratedFDeriv ℝ j q.val (γ t)‖ ≤ F) :
    ‖q.val (β 1)-q.val (γ 1)‖ ≤ |δ|^(s+1)*
      (twoFlowTaylorCoefficientBound R s Buv F +
        exponentialProductTailCoefficientBound s s (basisAlphabetWeight D)
          (linearWordPolynomial (D.basis.equivFun f)) (linearWordPolynomial (D.basis.equivFun g)) Bbr F +
        ((2^(s+1)*Bg)^(s+1)*F + exponentialTailCoefficientBound s s (basisAlphabetWeight D)
          (linearWordPolynomial (D.basis.equivFun (modelProduct f g))) Bbr F)) := by
  let Y := fun j => wordBracket X (modelBasisWord D j)
  have hY : ∀ j, ContDiffOn ℝ (⊤ : ℕ∞) (Y j) Ω :=
    fun j => G1.wordBracket_contDiffOn Ω.isOpen X hX (modelBasisWord D j)
  have hb := two_integralCurves_finiteExponential_bound (basisAlphabetWeight D) Ω Y hY
    (fun j => D.weight_bound j) δ (D.basis.equivFun f) (D.basis.equivFun g) U V hU hV hUcomb hVcomb
    α β hα hαmem hβ hβmem hβ₀ hseg hseg q hs hBuv hBbr hδ
    hUjet hVαjet hVβjet hbase hqαjet hqβjet
  rw [truncate_linear_basis_input,truncate_linear_basis_input] at hb
  have hx := hαmem 0 (hseg 0 (by simp))
  have he := differentialWordEvaluation_dilated_basis_BCH_exp D Ω X hX f g δ q hx
  have hb' : ‖q.val (β 1) -
      (differentialWordEvaluation Ω X hX
        (finitePolynomial (finiteExp (coefficientDilationHom δ (modelProduct f g).val))) q).val (α 0)‖ ≤
      |δ|^(s+1) * (twoFlowTaylorCoefficientBound R s Buv F +
        exponentialProductTailCoefficientBound s s (basisAlphabetWeight D)
          (linearWordPolynomial (D.basis.equivFun f))
          (linearWordPolynomial (D.basis.equivFun g)) Bbr F) := by
    calc
      _ = _ := congrArg (fun z => ‖q.val (β 1) - z‖) he
      _ ≤ _ := hb
  have hg := dilatedLieCurve_finiteExponential_bound (R := s+1) D Ω X hX
    (modelProduct f g) δ hδ γ hγmem hseg q le_rfl hBbr hwords
    (fun l j hj => by simpa only [hγ₀] using hbase l j (by omega)) hqγjet hγ
  rw [hγ₀,norm_sub_rev] at hg
  exact (norm_sub_le_norm_sub_add_norm_sub _ _ _).trans
    ((add_le_add hb' hg).trans_eq (by ring))
end RothschildStein.G3

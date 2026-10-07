-- Copyright (c) 2026 Scott Armstrong and Amélie Loher. All rights reserved.
-- Released under Apache 2.0 license as described in the file LICENSE.
module
public import RothschildStein.G3.GeneralLieBCHCurveComparison
public import RothschildStein.G3.CompactWordJetBounds
@[expose] public section
noncomputable section
open Set TopologicalSpace
open scoped BigOperators
namespace RothschildStein.G3

def generalLieBCHErrorCoefficient {a s : ℕ} {p : Fin a → ℕ+}
    (D : FreeModelData a s p) (f g : formalSpan a s p) (W F : ℝ) : ℝ :=
  let Buv := ((∑ j, |D.basis.equivFun f j|)+(∑ j, |D.basis.equivFun g j|))*W
  let Bg := (∑ j, |D.basis.equivFun (modelProduct f g) j|)*W
  twoFlowTaylorCoefficientBound (2*s+1) s Buv F +
    exponentialProductTailCoefficientBound s s (basisAlphabetWeight D)
      (linearWordPolynomial (D.basis.equivFun f)) (linearWordPolynomial (D.basis.equivFun g)) W F +
    ((2^(s+1)*Bg)^(s+1)*F + exponentialTailCoefficientBound s s (basisAlphabetWeight D)
      (linearWordPolynomial (D.basis.equivFun (modelProduct f g))) W F)

theorem generalLie_BCH_bound_of_compact_word_jets {a s N : ℕ} {p : Fin a → ℕ+}
    (D : FreeModelData a s p) (Ω : Opens (Fin N → ℝ))
    (X : Fin a → (Fin N → ℝ) → (Fin N → ℝ))
    (hX : ∀ i, ContDiffOn ℝ (⊤ : ℕ∞) (X i) Ω)
    (f g : formalSpan a s p) (δ : ℝ) (hs : 1 ≤ s)
    (α β γ : ℝ → (Fin N → ℝ))
    (hα : ∀ t ∈ Ioo (-2 : ℝ) 2, HasDerivAt α
      (finiteLieField D X ⟨finiteDilate δ f.val,finiteDilate_mem_formalSpan δ f.property⟩ (α t)) t)
    (hβ : ∀ t ∈ Ioo (-2 : ℝ) 2, HasDerivAt β
      (finiteLieField D X ⟨finiteDilate δ g.val,finiteDilate_mem_formalSpan δ g.property⟩ (β t)) t)
    (hγ : ∀ t ∈ Ioo (-2 : ℝ) 2, HasDerivAt γ
      (finiteLieField D X ⟨finiteDilate δ (modelProduct f g).val,
        finiteDilate_mem_formalSpan δ (modelProduct f g).property⟩ (γ t)) t)
    (hαΩ : ∀ t ∈ Ioo (-2 : ℝ) 2, α t ∈ Ω)
    (hβΩ : ∀ t ∈ Ioo (-2 : ℝ) 2, β t ∈ Ω)
    (hγΩ : ∀ t ∈ Ioo (-2 : ℝ) 2, γ t ∈ Ω)
    (hβ₀ : β 0 = α 1) (hγ₀ : γ 0 = α 0)
    (q : smoothOnFunctions Ω) {K : Set (Fin N → ℝ)} {W F : ℝ}
    (hKΩ : K ⊆ Ω) (hW : 0 ≤ W) (hδ : |δ| ≤ 1)
    (hαK : ∀ t ∈ Icc (0 : ℝ) 1, α t ∈ K)
    (hβK : ∀ t ∈ Icc (0 : ℝ) 1, β t ∈ K)
    (hγK : ∀ t ∈ Icc (0 : ℝ) 1, γ t ∈ K)
    (hwords : ∀ j k, k ≤ 2*s+1 → ∀ x ∈ K,
      ‖iteratedFDeriv ℝ k (wordBracket X (modelBasisWord D j)) x‖ ≤ W)
    (hq : ∀ k ≤ 2*s+1, ∀ x ∈ K, ‖iteratedFDeriv ℝ k q.val x‖ ≤ F) :
    ‖q.val (β 1)-q.val (γ 1)‖ ≤ |δ|^(s+1)*generalLieBCHErrorCoefficient D f g W F := by
  let U := finiteLieField D X ⟨finiteDilate δ f.val,finiteDilate_mem_formalSpan δ f.property⟩
  let V := finiteLieField D X ⟨finiteDilate δ g.val,finiteDilate_mem_formalSpan δ g.property⟩
  let Buv := ((∑ j, |D.basis.equivFun f j|)+(∑ j, |D.basis.equivFun g j|))*W
  let Bg := (∑ j, |D.basis.equivFun (modelProduct f g) j|)*W
  have hU := finiteLieField_contDiffOn D Ω X hX
    ⟨finiteDilate δ f.val,finiteDilate_mem_formalSpan δ f.property⟩
  have hV := finiteLieField_contDiffOn D Ω X hX
    ⟨finiteDilate δ g.val,finiteDilate_mem_formalSpan δ g.property⟩
  have hsum : ∀ z : formalSpan a s p, ∀ k ≤ 2*s+1, ∀ x ∈ K,
      (∑ j, |D.basis.equivFun z j| * ‖iteratedFDeriv ℝ k (wordBracket X (modelBasisWord D j)) x‖) ≤
        (∑ j, |D.basis.equivFun z j|)*W := by
    intro z k hk x hx
    exact compact_word_jet_sum_le D X z (fun j => hwords j k hk x hx)
  have hfB : (∑ j, |D.basis.equivFun f j|)*W ≤ Buv :=
    mul_le_mul_of_nonneg_right (le_add_of_nonneg_right (by positivity)) hW
  have hgB : (∑ j, |D.basis.equivFun g j|)*W ≤ Buv :=
    mul_le_mul_of_nonneg_right (le_add_of_nonneg_left (by positivity)) hW
  have hsmall : ∀ z : formalSpan a s p, ∀ k ≤ 2*s+1, ∀ x ∈ K,
      ‖iteratedFDeriv ℝ k (finiteLieField D X
        ⟨finiteDilate δ z.val,finiteDilate_mem_formalSpan δ z.property⟩) x‖ ≤
        |δ| * ((∑ j, |D.basis.equivFun z j|)*W) := by
    intro z k hk x hx
    exact (norm_iteratedFDeriv_dilatedLieField_le D Ω X hX z δ hδ k (hKΩ hx)).trans
      (mul_le_mul_of_nonneg_left (hsum z k hk x hx) (abs_nonneg δ))
  have hseg : ∀ t ∈ Icc (0 : ℝ) 1, t ∈ Ioo (-2 : ℝ) 2 := by
    intro t ht; constructor <;> linarith [ht.1,ht.2]
  exact generalLie_BCH_integralCurves_comparison_bound D Ω X hX f g δ U V hU hV
    (dilatedLieField_eq_weighted_combination D X f δ) (dilatedLieField_eq_weighted_combination D X g δ)
    α β γ hα hβ hγ hαΩ hβΩ hγΩ hβ₀ hγ₀ hseg q le_rfl (by dsimp [Buv]; positivity) hW hδ
    (fun t ht k hk => (hsmall f k hk _ (hαK t ht)).trans (mul_le_mul_of_nonneg_left hfB (abs_nonneg δ)))
    (fun t ht k hk => (hsmall g k hk _ (hαK t ht)).trans (mul_le_mul_of_nonneg_left hgB (abs_nonneg δ)))
    (fun t ht k hk => (hsmall g k hk _ (hβK t ht)).trans (mul_le_mul_of_nonneg_left hgB (abs_nonneg δ)))
    (fun j k hk => hwords j k (by omega) _ (hαK 0 (by simp)))
    (fun t ht k hk => hq k hk _ (hαK t ht)) (fun t ht k hk => hq k hk _ (hβK t ht))
    (fun t ht k hk => hsum (modelProduct f g) k (by omega) _ (hγK t ht))
    (fun t ht k hk => hq k (by omega) _ (hγK t ht))
end RothschildStein.G3

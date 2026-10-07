-- Copyright (c) 2026 Scott Armstrong and Amélie Loher. All rights reserved.
-- Released under Apache 2.0 license as described in the file LICENSE.
module
public import RothschildStein.G3.GeneralLieBCHPrimitiveJets
public import RothschildStein.G3.PrimitiveFlowDisplacement
@[expose] public section
noncomputable section
open Set TopologicalSpace
open scoped BigOperators
namespace RothschildStein.G3

def generalLieTravelBudget {a s : ℕ} {p : Fin a → ℕ+}
    (D : FreeModelData a s p) (f : formalSpan a s p) (B : ℝ) : ℝ :=
  (∑ j, |D.basis.equivFun f j|) * primitiveWordJetBudget D (3*s+2) B

theorem generalLieTravelBudget_nonneg {a s : ℕ} {p : Fin a → ℕ+}
    (D : FreeModelData a s p) (f : formalSpan a s p) {B : ℝ} (hB : 0 ≤ B) :
    0 ≤ generalLieTravelBudget D f B := by
  dsimp [generalLieTravelBudget,primitiveWordJetBudget]
  positivity

/-- Travel of a dilated retained Lie input has a numerical budget on the
whole open buffer. Its bound uses no absolute spatial coordinate. -/
theorem dilatedLieCurve_displacement_le {a s N : ℕ} {p : Fin a → ℕ+}
    (D : FreeModelData a s p) (Ω : Opens (Fin N → ℝ))
    (X : Fin a → (Fin N → ℝ) → (Fin N → ℝ))
    (hX : ∀ i, ContDiffOn ℝ (⊤ : ℕ∞) (X i) Ω)
    (f : formalSpan a s p) (δ : ℝ) {B : ℝ} (hB : 0 ≤ B) (hδ : |δ| ≤ 1)
    (α : ℝ → (Fin N → ℝ))
    (hα : ∀ t ∈ Ioo (-2 : ℝ) 2, HasDerivAt α
      (finiteLieField D X ⟨finiteDilate δ f.val,finiteDilate_mem_formalSpan δ f.property⟩ (α t)) t)
    (hαΩ : ∀ t ∈ Ioo (-2 : ℝ) 2, α t ∈ Ω)
    (hjets : ∀ x ∈ Ω, ∀ i k, k ≤ 3*s+2 → ‖iteratedFDeriv ℝ k (X i) x‖ ≤ B)
    {t : ℝ} (ht : t ∈ Ioo (-2 : ℝ) 2) :
    ‖α t-α 0‖ ≤ |δ| * generalLieTravelBudget D f B * |t| := by
  apply primitiveFlow_displacement_le (by norm_num : (0 : ℝ) < 2)
    (fun z => α z.2) (α 0) rfl (fun v hv => ⟨hα v hv,hαΩ v hv⟩) _ ht
  intro y hy
  have hw : ∀ j, ‖iteratedFDeriv ℝ 0 (wordBracket X (modelBasisWord D j)) y‖ ≤
      primitiveWordJetBudget D (3*s+2) B := by
    intro j
    exact norm_basisWord_jet_le_uniform_sum D Ω X hX hy hB
      (fun i n hn => hjets y hy i n hn) 0 (by omega) j
  have hb := norm_iteratedFDeriv_dilatedLieField_le D Ω X hX f δ hδ 0 hy
  simpa only [norm_iteratedFDeriv_zero,generalLieTravelBudget] using
    hb.trans (mul_le_mul_of_nonneg_left (compact_word_jet_sum_le D X f hw) (abs_nonneg δ))
end RothschildStein.G3

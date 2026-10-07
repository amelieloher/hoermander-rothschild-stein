-- Copyright (c) 2026 Scott Armstrong and Amélie Loher. All rights reserved.
-- Released under Apache 2.0 license as described in the file LICENSE.
module
public import RothschildStein.G3.GeneralLieBCHCompactJets
public import RothschildStein.G3.PrimitiveFiniteJetBCHComparison
@[expose] public section
noncomputable section
open Set TopologicalSpace
namespace RothschildStein.G3

/-- Arbitrary Lie inputs use only primitive ambient jets through 3s+2. -/
theorem generalLie_BCH_bound_of_finite_primitive_jets {a s N : ℕ} {p : Fin a → ℕ+}
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
    (q : smoothOnFunctions Ω) {K : Set (Fin N → ℝ)} {Bx F : ℝ}
    (hKΩ : K ⊆ Ω) (hBx : 0 ≤ Bx) (hδ : |δ| ≤ 1)
    (hαK : ∀ t ∈ Icc (0 : ℝ) 1, α t ∈ K)
    (hβK : ∀ t ∈ Icc (0 : ℝ) 1, β t ∈ K)
    (hγK : ∀ t ∈ Icc (0 : ℝ) 1, γ t ∈ K)
    (hXjets : ∀ i k, k ≤ 3*s+2 → ∀ x ∈ K,
      ‖iteratedFDeriv ℝ k (X i) x‖ ≤ Bx)
    (hq : ∀ k ≤ 2*s+1, ∀ x ∈ K, ‖iteratedFDeriv ℝ k q.val x‖ ≤ F) :
    ‖q.val (β 1)-q.val (γ 1)‖ ≤ |δ|^(s+1)*generalLieBCHErrorCoefficient D f g (primitiveWordJetBudget D (3*s+2) Bx) F := by
  have hW : 0 ≤ primitiveWordJetBudget D (3*s+2) Bx :=
    Finset.sum_nonneg (fun j _ => mul_nonneg (by positivity) (pow_nonneg hBx _))
  apply generalLie_BCH_bound_of_compact_word_jets D Ω X hX f g δ hs
    α β γ hα hβ hγ hαΩ hβΩ hγΩ hβ₀ hγ₀ q hKΩ hW hδ hαK hβK hγK
  · intro j k hk x hx
    exact norm_basisWord_jet_le_uniform_sum D Ω X hX (hKΩ hx) hBx
      (fun i n hn => hXjets i n hn x hx) k (by omega) j
  · exact hq
end RothschildStein.G3

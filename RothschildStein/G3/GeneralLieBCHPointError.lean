-- Copyright (c) 2026 Scott Armstrong and Amélie Loher. All rights reserved.
-- Released under Apache 2.0 license as described in the file LICENSE.
module
public import RothschildStein.G3.GeneralLieBCHPrimitiveJets
public import RothschildStein.G3.TranslatedCoordinateJetBounds
@[expose] public section
noncomputable section
open Set TopologicalSpace
namespace RothschildStein.G3

/-- Arbitrary retained Lie inputs have a numerical point error, independent
of the absolute location of the spatial buffer. -/
theorem generalLie_BCH_point_error_of_finite_primitive_jets {a s N : ℕ} {p : Fin a → ℕ+}
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
    {K : Set (Fin N → ℝ)} {Bx r : ℝ} (x₀ : Fin N → ℝ)
    (hKr : K ⊆ Metric.closedBall x₀ r)
    (hKΩ : K ⊆ Ω) (hBx : 0 ≤ Bx) (hδ : |δ| ≤ 1)
    (hαK : ∀ t ∈ Icc (0 : ℝ) 1, α t ∈ K)
    (hβK : ∀ t ∈ Icc (0 : ℝ) 1, β t ∈ K)
    (hγK : ∀ t ∈ Icc (0 : ℝ) 1, γ t ∈ K)
    (hXjets : ∀ i k, k ≤ 3*s+2 → ∀ x ∈ K,
      ‖iteratedFDeriv ℝ k (X i) x‖ ≤ Bx)
 :
    ‖β 1-γ 1‖ ≤ |δ|^(s+1)*generalLieBCHErrorCoefficient D f g (primitiveWordJetBudget D (3*s+2) Bx) (max r 1) := by
  have hcoef : 0 ≤ generalLieBCHErrorCoefficient D f g
      (primitiveWordJetBudget D (3*s+2) Bx) (max r 1) := by
    dsimp [generalLieBCHErrorCoefficient,primitiveWordJetBudget,twoFlowTaylorCoefficientBound,
      exponentialProductTailCoefficientBound,exponentialTailCoefficientBound]
    positivity
  apply (pi_norm_le_iff_of_nonneg (mul_nonneg (by positivity) hcoef)).mpr
  intro j
  have he := generalLie_BCH_bound_of_finite_primitive_jets D Ω X hX f g δ hs
    α β γ hα hβ hγ hαΩ hβΩ hγΩ hβ₀ hγ₀ (translatedCoordinateTest Ω x₀ j)
    hKΩ hBx hδ hαK hβK hγK hXjets
    (fun k _ x hx => norm_translatedCoordinateTest_jet_le Ω x₀ j (hKr hx) k)
  simpa [translatedCoordinateTest,Pi.sub_apply] using he
end RothschildStein.G3

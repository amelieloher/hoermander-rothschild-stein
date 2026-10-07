-- Copyright (c) 2026 Scott Armstrong and Amélie Loher. All rights reserved.
-- Released under Apache 2.0 license as described in the file LICENSE.
module

public import RothschildStein.S.TestPairing
public import RothschildStein.S.Sobolev

set_option autoImplicit false
set_option relaxedAutoImplicit false
@[expose] public section
noncomputable section
open Set MeasureTheory TopologicalSpace Filter
open scoped BigOperators Topology ENNReal
namespace RothschildStein.S
variable {n m : ℕ}

/-- A weak word derivative has closed graph in Lᵖ × Lᵖ
(BB Prop. 2.5, p. 69). -/
theorem isClosed_weakWordGraph (Ω : Opens (Fin n → ℝ))
    (X : Fin m → (Fin n → ℝ) → (Fin n → ℝ))
    (hX : ∀ i, ContDiffOn ℝ (⊤ : ℕ∞) (X i) (Ω : Set (Fin n → ℝ)))
    (I : List (Fin m)) (p r : ℝ≥0∞)
    [Fact (1 ≤ p)] [Fact (1 ≤ r)] [ENNReal.HolderConjugate p r] :
    IsClosed {v : Lp ℝ p (volume.restrict (Ω : Set (Fin n → ℝ))) ×
      Lp ℝ p (volume.restrict (Ω : Set (Fin n → ℝ))) |
      hasWeakWordDeriv X Ω I v.1 v.2} := by
  have hl : ∀ f : Lp ℝ p (volume.restrict (Ω : Set (Fin n → ℝ))),
      LocallyIntegrableOn f (Ω : Set (Fin n → ℝ)) volume := fun f =>
    locallyIntegrableOn_of_locallyIntegrable_restrict ((Lp.memLp f).locallyIntegrable Fact.out)
  have hc : IsClosed {v : Lp ℝ p (volume.restrict (Ω : Set (Fin n → ℝ))) ×
      Lp ℝ p (volume.restrict (Ω : Set (Fin n → ℝ))) |
      ∀ ψ : TestFunction Ω ℝ (⊤ : ℕ∞),
        lpTestPairingCLM Ω p r ψ v.2 =
          lpTestPairingCLM Ω p r (wordTransposeTest Ω X hX I ψ) v.1} := by
    simp only [ofPred_forall]
    apply isClosed_iInter
    intro ψ
    exact isClosed_eq ((lpTestPairingCLM Ω p r ψ).continuous.comp continuous_snd)
      ((lpTestPairingCLM Ω p r (wordTransposeTest Ω X hX I ψ)).continuous.comp continuous_fst)
  convert hc using 1
  ext v
  simp only [mem_ofPred_eq]
  constructor
  · intro h ψ
    rw [lpTestPairingCLM_apply, lpTestPairingCLM_apply]
    simp_rw [wordTransposeTest_apply]
    exact h.2.2 ψ
  · intro h
    refine ⟨hl v.1, hl v.2, fun ψ => ?_⟩
    have hi := h ψ
    rw [lpTestPairingCLM_apply, lpTestPairingCLM_apply] at hi
    simpa only [wordTransposeTest_apply] using hi

/-- Simultaneous Lᵖ limits retain the weak word derivative
(BB Prop. 2.5, p. 69). -/
theorem hasWeakWordDeriv_lp_limit {α : Type*} {l : Filter α} [NeBot l]
    (Ω : Opens (Fin n → ℝ))
    (X : Fin m → (Fin n → ℝ) → (Fin n → ℝ))
    (hX : ∀ i, ContDiffOn ℝ (⊤ : ℕ∞) (X i) (Ω : Set (Fin n → ℝ)))
    (I : List (Fin m)) (p r : ℝ≥0∞)
    [Fact (1 ≤ p)] [Fact (1 ≤ r)] [ENNReal.HolderConjugate p r]
    (F G : α → Lp ℝ p (volume.restrict (Ω : Set (Fin n → ℝ))))
    (f g : Lp ℝ p (volume.restrict (Ω : Set (Fin n → ℝ))))
    (h : ∀ᶠ j in l, hasWeakWordDeriv X Ω I (F j) (G j))
    (hF : Tendsto F l (𝓝 f)) (hG : Tendsto G l (𝓝 g)) :
    hasWeakWordDeriv X Ω I f g :=
  (isClosed_weakWordGraph Ω X hX I p r).mem_of_tendsto (hF.prodMk_nhds hG) h

end RothschildStein.S

-- Copyright (c) 2026 Scott Armstrong and Amélie Loher. All rights reserved.
-- Released under Apache 2.0 license as described in the file LICENSE.
module

public import RothschildStein.H3.WeakWordConditional
public import RothschildStein.H3.ConvolutionEquationLimit
public import RothschildStein.H3.WeakDriftOperatorUniqueness

set_option autoImplicit false
set_option relaxedAutoImplicit false
@[expose] public section
noncomputable section
namespace RothschildStein.H3
open MeasureTheory Filter TopologicalSpace
open scoped ENNReal Topology

/-- A smooth convolution approximation with uniform jet estimates gives
local Sobolev solvability, the almost-everywhere equation, and every jet
bound under the stated kernel hypotheses (BB p. 374). -/
theorem local_solution_of_convolution_estimates {n q : ℕ}
    (Ω : Opens (Fin n → ℝ))
    (X : Fin (q+1) → (Fin n → ℝ) → (Fin n → ℝ))
    (hX : ∀ i, ContDiffOn ℝ (⊤ : ℕ∞) (X i) (Ω : Set (Fin n → ℝ)))
    (p r : ℝ≥0∞)
    [Fact (1 ≤ p)] [Fact (1 ≤ r)] [ENNReal.HolderConjugate p r]
    (f v : ℕ → (Fin n → ℝ) → ℝ) (F u : (Fin n → ℝ) → ℝ)
    (hf : ∀ j, MemLp (f j) p volume) (hF : MemLp F p volume)
    (hv : ∀ j, ContDiffOn ℝ (⊤ : ℕ∞) (v j) (Ω : Set (Fin n → ℝ)))
    (hvl : ∀ j, MemLp (v j) p (volume.restrict (Ω : Set (Fin n → ℝ))))
    (hu : MemLp u p (volume.restrict (Ω : Set (Fin n → ℝ))))
    (hj : ∀ I ∈ wordFamily driftWeight 2, ∀ j,
      MemLp (wordDerivative X I (v j)) p (volume.restrict (Ω : Set (Fin n → ℝ))))
    (hft : Tendsto (fun j => eLpNorm (f j - F) p volume) atTop (𝓝 0))
    (hut : Tendsto (fun j => eLpNorm (v j - u) p
      (volume.restrict (Ω : Set (Fin n → ℝ)))) atTop (𝓝 0))
    (C : List (Fin (q+1)) → ℝ) (hC : ∀ I ∈ wordFamily driftWeight 2, 0 ≤ C I)
    (hdiff : ∀ I ∈ wordFamily driftWeight 2, ∀ j l,
      eLpNorm (wordDerivative X I (v j) - wordDerivative X I (v l)) p
        (volume.restrict (Ω : Set (Fin n → ℝ))) ≤
          ENNReal.ofReal (C I) * eLpNorm (f j - f l) p volume)
    (hbound : ∀ I ∈ wordFamily driftWeight 2, ∀ j,
      eLpNorm (wordDerivative X I (v j)) p (volume.restrict (Ω : Set (Fin n → ℝ))) ≤
        ENNReal.ofReal (C I) * eLpNorm (f j) p volume)
    (heq : ∀ j (ψ : TestFunction Ω ℝ (⊤ : ℕ∞)),
      (∫ x in (Ω : Set (Fin n → ℝ)), f j x * ψ x) =
        ∫ x in (Ω : Set (Fin n → ℝ)), v j x * sumSquaresWithDriftTranspose X ψ x) :
    memSobolevX driftWeight X Ω 2 p u ∧
      ∃ D : WeakDriftOperatorData X Ω p u,
        D.operator =ᵐ[volume.restrict (Ω : Set (Fin n → ℝ))] F ∧
        ∀ I ∈ wordFamily driftWeight 2, weakWordENorm X Ω I p u ≤
          ENNReal.ofReal (C I) * eLpNorm F p volume := by
  have hw : ∀ I ∈ wordFamily driftWeight 2, ∃ g,
      hasWeakWordDeriv X Ω I u g ∧
        MemLp g p (volume.restrict (Ω : Set (Fin n → ℝ))) ∧
        eLpNorm g p (volume.restrict (Ω : Set (Fin n → ℝ))) ≤
          ENNReal.ofReal (C I) * eLpNorm F p volume := by
    intro I hI
    exact weak_word_of_convolution_estimates Ω X hX I p r f v F u hf hF hv hvl hu
      (hj I hI) hft hut (C I) (hC I hI) (hdiff I hI) (hbound I hI)
  have hs : memSobolevX driftWeight X Ω 2 p u := by
    refine ⟨hu, fun I hI => ?_⟩
    obtain ⟨g, hg, hgl, _⟩ := hw I hI
    exact ⟨g, hg, hgl⟩
  obtain ⟨D⟩ := exists_weakDriftOperatorData X Ω p u hs
  have hfl : ∀ j, MemLp (f j) p (volume.restrict (Ω : Set (Fin n → ℝ))) :=
    fun j => (hf j).mono_measure Measure.restrict_le_self
  have hFl := hF.mono_measure (Measure.restrict_le_self (s := (Ω : Set (Fin n → ℝ))))
  have hftl : Tendsto (fun j => eLpNorm (f j - F) p
      (volume.restrict (Ω : Set (Fin n → ℝ)))) atTop (𝓝 0) := by
    exact tendsto_of_tendsto_of_tendsto_of_le_of_le tendsto_const_nhds hft
      (fun _ => bot_le) (fun j => eLpNorm_mono_measure (f j - F) Measure.restrict_le_self)
  have he := equation_of_lp_pairing_limits Ω X hX p r f v F u
    hfl hvl hFl hu hftl hut heq
  refine ⟨hs, D, D.operator_ae_eq_of_pairing hX Fact.out hFl he, ?_⟩
  intro I hI
  obtain ⟨g, hg, _, hb⟩ := hw I hI
  rw [S.weakWordENorm_eq X Ω I p u g hg]
  exact hb

end RothschildStein.H3

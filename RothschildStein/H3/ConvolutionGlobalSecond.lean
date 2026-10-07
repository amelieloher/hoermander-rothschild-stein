-- Copyright (c) 2026 Scott Armstrong and Amélie Loher. All rights reserved.
-- Released under Apache 2.0 license as described in the file LICENSE.
module

public import RothschildStein.H3.GlobalConvolutionWord
public import RothschildStein.H3.DriftSecondWeakNorm

set_option autoImplicit false
set_option relaxedAutoImplicit false
@[expose] public section
noncomputable section
namespace RothschildStein.H3
open Set MeasureTheory Filter TopologicalSpace
open scoped ENNReal Topology
open G2

/-- The complete global second norm, including drift and mixed
words, obeys the uniform singular-integral estimate of the approximants.
Each global weak derivative is constructed by Lp completeness. -/
theorem global_second_of_convolution_estimates {n q : ℕ}
    (G : HomogeneousGroup n) (H : H1.StandingHypotheses G q)
    {α : ℝ} (K : (Fin n → ℝ) → ℝ) (hK : PositiveType G α K)
    (ν : HomogeneousNorm G) (h1 : ν.c = 1) (hsym : ν.Symmetric)
    {ρ : ℝ} (hρ : 0 < ρ)
    (p r : ℝ≥0∞) [Fact (1 ≤ p)] [Fact (1 ≤ r)] [ENNReal.HolderConjugate p r]
    (f : ℕ → (Fin n → ℝ) → ℝ) (F : (Fin n → ℝ) → ℝ)
    (hF : MemLp F p volume)
    (hfs : ∀ j, ContDiff ℝ (⊤ : ℕ∞) (f j)) (hfc : ∀ j, HasCompactSupport (f j))
    (hsF : ∀ᵐ y ∂volume, ρ ≤ ν y → F y = 0)
    (hsf : ∀ j, ∀ᵐ y ∂volume, ρ ≤ ν y → f j y = 0)
    (hft : Tendsto (fun j => eLpNorm (f j-F) p volume) atTop (𝓝 0))
    (C : ℝ) (hC : 0 ≤ C)
    (hdiff : ∀ I : List (Fin (q+1)), wordWeight driftWeight I = 2 → ∀ j l,
      eLpNorm (wordDerivative H.fields I (groupConvolution G (f j) K)-
        wordDerivative H.fields I (groupConvolution G (f l) K)) p volume ≤
          ENNReal.ofReal C*eLpNorm (f j-f l) p volume)
    (hbound : ∀ I : List (Fin (q+1)), wordWeight driftWeight I = 2 → ∀ j,
      eLpNorm (wordDerivative H.fields I (groupConvolution G (f j) K)) p volume ≤
        ENNReal.ofReal C*eLpNorm (f j) p volume) :
    (∀ I : List (Fin (q+1)), wordWeight driftWeight I = 2 →
      ∃ g : (Fin n → ℝ) → ℝ,
        hasWeakWordDeriv H.fields ⊤ I (groupConvolution G F K) g ∧ MemLp g p volume) ∧
      driftSecondWeakENorm H.fields ⊤ p (groupConvolution G F K) ≤
        (driftSecondWordFamily q).card * ENNReal.ofReal C * eLpNorm F p volume := by
  have hw := fun I hI => global_word_of_convolution_estimates G H K hK ν h1 hsym
    hρ I p r f F hF hfs hfc hsF hsf hft C hC (hdiff I hI) (hbound I hI)
  refine ⟨fun I hI => ?_,?_⟩
  · obtain ⟨g,hg,hgl,_⟩ := hw I hI
    exact ⟨g,hg,hgl⟩
  · have hb : ∀ I : List (Fin (q+1)), wordWeight driftWeight I = 2 →
        weakWordENorm H.fields ⊤ I p (groupConvolution G F K) ≤
          ENNReal.ofReal C*eLpNorm F p volume := by
      intro I hI
      obtain ⟨g,hg,_,hbg⟩ := hw I hI
      rw [S.weakWordENorm_eq H.fields ⊤ I p (groupConvolution G F K) g hg]
      simpa using hbg
    simpa only [Semigroup.mul_assoc] using driftSecondWeakENorm_le_of_word_bounds H.fields ⊤ p
      (groupConvolution G F K) (ENNReal.ofReal C*eLpNorm F p volume) hb

end RothschildStein.H3

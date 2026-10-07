-- Copyright (c) 2026 Scott Armstrong and Amélie Loher. All rights reserved.
-- Released under Apache 2.0 license as described in the file LICENSE.
module

public import RothschildStein.H3.CauchyWeakJet
public import RothschildStein.H3.CauchyEstimateTransfer
public import RothschildStein.H3.InterpolationDensity

set_option autoImplicit false
set_option relaxedAutoImplicit false
@[expose] public section
noncomputable section
namespace RothschildStein.H3
open MeasureTheory Filter TopologicalSpace
open scoped ENNReal Topology

/-- Local weak derivatives and their bounds follow from smooth
convolution approximation and the exact uniform convolution difference
estimate. No derivative of the limit is supplied (BB p. 374). -/
theorem weak_word_of_convolution_estimates {n m : ℕ}
    (Ω : Opens (Fin n → ℝ))
    (X : Fin m → (Fin n → ℝ) → (Fin n → ℝ))
    (hX : ∀ i, ContDiffOn ℝ (⊤ : ℕ∞) (X i) (Ω : Set (Fin n → ℝ)))
    (I : List (Fin m)) (p r : ℝ≥0∞)
    [Fact (1 ≤ p)] [Fact (1 ≤ r)] [ENNReal.HolderConjugate p r]
    (f v : ℕ → (Fin n → ℝ) → ℝ) (F u : (Fin n → ℝ) → ℝ)
    (hf : ∀ j, MemLp (f j) p volume) (hF : MemLp F p volume)
    (hv : ∀ j, ContDiffOn ℝ (⊤ : ℕ∞) (v j) (Ω : Set (Fin n → ℝ)))
    (hvl : ∀ j, MemLp (v j) p (volume.restrict (Ω : Set (Fin n → ℝ))))
    (hu : MemLp u p (volume.restrict (Ω : Set (Fin n → ℝ))))
    (hj : ∀ j, MemLp (wordDerivative X I (v j)) p
      (volume.restrict (Ω : Set (Fin n → ℝ))))
    (hft : Tendsto (fun j => eLpNorm (f j - F) p volume) atTop (𝓝 0))
    (hut : Tendsto (fun j => eLpNorm (v j - u) p
      (volume.restrict (Ω : Set (Fin n → ℝ)))) atTop (𝓝 0))
    (C : ℝ) (hC : 0 ≤ C)
    (hdiff : ∀ j l, eLpNorm (wordDerivative X I (v j) - wordDerivative X I (v l))
      p (volume.restrict (Ω : Set (Fin n → ℝ))) ≤
        ENNReal.ofReal C * eLpNorm (f j - f l) p volume)
    (hbound : ∀ j, eLpNorm (wordDerivative X I (v j)) p
      (volume.restrict (Ω : Set (Fin n → ℝ))) ≤
        ENNReal.ofReal C * eLpNorm (f j) p volume) :
    ∃ g : (Fin n → ℝ) → ℝ, hasWeakWordDeriv X Ω I u g ∧
      MemLp g p (volume.restrict (Ω : Set (Fin n → ℝ))) ∧
      eLpNorm g p (volume.restrict (Ω : Set (Fin n → ℝ))) ≤
        ENNReal.ofReal C * eLpNorm F p volume := by
  have ht := (Lp.tendsto_Lp_iff_tendsto_eLpNorm'' f hf F hF).mpr hft
  have hc := lp_cauchy_of_difference_estimate volume
    (volume.restrict (Ω : Set (Fin n → ℝ))) p f
    (fun j => wordDerivative X I (v j)) hf hj C hC ht.cauchySeq hdiff
  obtain ⟨g, hg, hgl, hgt⟩ := weak_word_of_cauchy_classical_jets Ω X hX I p r
    v u hv hvl hu hj hc hut
  refine ⟨g, hg, hgl, ?_⟩
  have hn := eLpNorm_tendsto_of_lp_difference
    (volume.restrict (Ω : Set (Fin n → ℝ))) Fact.out hj hgl hgt
  have hfn := eLpNorm_tendsto_of_lp_difference volume Fact.out hf hF hft
  have hr := ENNReal.Tendsto.const_mul (a := ENNReal.ofReal C) hfn
    (Or.inr ENNReal.ofReal_ne_top)
  exact le_of_tendsto_of_tendsto hn hr (Eventually.of_forall hbound)

end RothschildStein.H3

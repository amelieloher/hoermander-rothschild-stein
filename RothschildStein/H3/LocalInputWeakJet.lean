-- Copyright (c) 2026 Scott Armstrong and Amélie Loher. All rights reserved.
-- Released under Apache 2.0 license as described in the file LICENSE.
module

public import RothschildStein.H3.CauchyWeakJet
public import RothschildStein.S.LocalConvergence

set_option autoImplicit false
set_option relaxedAutoImplicit false
@[expose] public section
noncomputable section
namespace RothschildStein.H3
open Set MeasureTheory Filter TopologicalSpace
open scoped ENNReal Topology

/-- Global Cauchy jets have a global weak Lp limit even when
the input functions converge only locally in Lp. No global input norm is
required, so this applies to convolutions with nonintegrable tails. -/
theorem weak_word_of_global_cauchy_jets_and_local_input {n m : ℕ}
    (Ω : Opens (Fin n → ℝ))
    (X : Fin m → (Fin n → ℝ) → (Fin n → ℝ))
    (hX : ∀ i, ContDiffOn ℝ (⊤ : ℕ∞) (X i) (Ω : Set (Fin n → ℝ)))
    (I : List (Fin m)) (p r : ℝ≥0∞)
    [Fact (1 ≤ p)] [Fact (1 ≤ r)] [ENNReal.HolderConjugate p r]
    (v : ℕ → (Fin n → ℝ) → ℝ) (u : (Fin n → ℝ) → ℝ)
    (hv : ∀ j, ContDiffOn ℝ (⊤ : ℕ∞) (v j) (Ω : Set (Fin n → ℝ)))
    (hu : LocallyIntegrableOn u (Ω : Set (Fin n → ℝ)) volume)
    (hvl : ∀ U : Opens (Fin n → ℝ), IsCompact (closure (U : Set (Fin n → ℝ))) →
      closure (U : Set (Fin n → ℝ)) ⊆ Ω →
      ∀ j, MemLp (v j) p (volume.restrict (U : Set (Fin n → ℝ))))
    (hul : ∀ U : Opens (Fin n → ℝ), IsCompact (closure (U : Set (Fin n → ℝ))) →
      closure (U : Set (Fin n → ℝ)) ⊆ Ω →
      MemLp u p (volume.restrict (U : Set (Fin n → ℝ))))
    (hut : ∀ U : Opens (Fin n → ℝ), IsCompact (closure (U : Set (Fin n → ℝ))) →
      closure (U : Set (Fin n → ℝ)) ⊆ Ω →
      Tendsto (fun j => eLpNorm (fun x => v j x-u x) p
        (volume.restrict (U : Set (Fin n → ℝ)))) atTop (𝓝 0))
    (hj : ∀ j, MemLp (wordDerivative X I (v j)) p
      (volume.restrict (Ω : Set (Fin n → ℝ))))
    (hc : CauchySeq (fun j => (hj j).toLp (wordDerivative X I (v j)))) :
    ∃ g : (Fin n → ℝ) → ℝ, hasWeakWordDeriv X Ω I u g ∧
      MemLp g p (volume.restrict (Ω : Set (Fin n → ℝ))) ∧
      Tendsto (fun j => eLpNorm (wordDerivative X I (v j)-g) p
        (volume.restrict (Ω : Set (Fin n → ℝ)))) atTop (𝓝 0) := by
  obtain ⟨g,hg⟩ := cauchySeq_tendsto_of_complete hc
  have hgl : MemLp g p (volume.restrict (Ω : Set (Fin n → ℝ))) := Lp.memLp g
  have hgt : Tendsto (fun j => eLpNorm (wordDerivative X I (v j)-(g : (Fin n → ℝ) → ℝ)) p
      (volume.restrict (Ω : Set (Fin n → ℝ)))) atTop (𝓝 0) := by
    apply (Lp.tendsto_Lp_iff_tendsto_eLpNorm''
      (fun j => wordDerivative X I (v j)) hj g hgl).mp
    simpa only [Lp.toLp_coeFn] using hg
  refine ⟨g,⟨hu,
    locallyIntegrableOn_of_locallyIntegrable_restrict (hgl.locallyIntegrable Fact.out),?_⟩,
    hgl,hgt⟩
  intro ψ
  have hleft := S.tendsto_testIntegral_of_tendsto_eLpNorm Ω p r ψ
    (fun j => wordDerivative X I (v j)) g hj hgl hgt
  have hright := S.tendsto_testIntegral_of_localLp Ω p v u hvl hul hut
    (wordTransposeTest Ω X hX I ψ)
  simp only [S.wordTransposeTest_apply] at hright
  apply tendsto_nhds_unique hleft
  exact hright.congr (fun j => (S.hasWeakWordDeriv_classical Ω X hX I (v j) (hv j)).2.2 ψ |>.symm)

end RothschildStein.H3

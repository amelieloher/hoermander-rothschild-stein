-- Copyright (c) 2026 Scott Armstrong and Amélie Loher. All rights reserved.
-- Released under Apache 2.0 license as described in the file LICENSE.
module

public import RothschildStein.S.WeakGraph
public import RothschildStein.S.ClassicalWords
public import RothschildStein.S.WeakDeriv
public import Mathlib.MeasureTheory.Function.LpSpace.Complete

set_option autoImplicit false
set_option relaxedAutoImplicit false
@[expose] public section
noncomputable section
namespace RothschildStein.H3
open MeasureTheory Filter TopologicalSpace
open scoped ENNReal Topology

/-- Completeness and the closed weak graph turn Cauchy classical
word jets into weak derivatives of the actual Lp limit (BB p. 374). -/
theorem weak_word_of_cauchy_classical_jets {n m : ℕ}
    (Ω : Opens (Fin n → ℝ))
    (X : Fin m → (Fin n → ℝ) → (Fin n → ℝ))
    (hX : ∀ i, ContDiffOn ℝ (⊤ : ℕ∞) (X i) (Ω : Set (Fin n → ℝ)))
    (I : List (Fin m)) (p r : ℝ≥0∞)
    [Fact (1 ≤ p)] [Fact (1 ≤ r)] [ENNReal.HolderConjugate p r]
    (v : ℕ → (Fin n → ℝ) → ℝ) (u : (Fin n → ℝ) → ℝ)
    (hv : ∀ j, ContDiffOn ℝ (⊤ : ℕ∞) (v j) (Ω : Set (Fin n → ℝ)))
    (hvl : ∀ j, MemLp (v j) p (volume.restrict (Ω : Set (Fin n → ℝ))))
    (hu : MemLp u p (volume.restrict (Ω : Set (Fin n → ℝ))))
    (hj : ∀ j, MemLp (wordDerivative X I (v j)) p
      (volume.restrict (Ω : Set (Fin n → ℝ))))
    (hc : CauchySeq (fun j => (hj j).toLp (wordDerivative X I (v j))))
    (ht : Tendsto (fun j => eLpNorm (v j - u) p
      (volume.restrict (Ω : Set (Fin n → ℝ)))) atTop (𝓝 0)) :
    ∃ g : (Fin n → ℝ) → ℝ, hasWeakWordDeriv X Ω I u g ∧
      MemLp g p (volume.restrict (Ω : Set (Fin n → ℝ))) ∧
      Tendsto (fun j => eLpNorm (wordDerivative X I (v j) - g) p
        (volume.restrict (Ω : Set (Fin n → ℝ)))) atTop (𝓝 0) := by
  obtain ⟨g, hg⟩ := cauchySeq_tendsto_of_complete hc
  have hV := (Lp.tendsto_Lp_iff_tendsto_eLpNorm'' v hvl u hu).mpr ht
  have hweak := S.hasWeakWordDeriv_lp_limit Ω X hX I p r
    (fun j => (hvl j).toLp (v j))
    (fun j => (hj j).toLp (wordDerivative X I (v j)))
    (hu.toLp u) g (Eventually.of_forall (fun j =>
      S.hasWeakWordDeriv_congr_ae X Ω
        (S.hasWeakWordDeriv_classical Ω X hX I (v j) (hv j))
        (hvl j).coeFn_toLp.symm (hj j).coeFn_toLp.symm)) hV hg
  refine ⟨g, S.hasWeakWordDeriv_congr_ae X Ω hweak hu.coeFn_toLp Filter.EventuallyEq.rfl, Lp.memLp g, ?_⟩
  apply (Lp.tendsto_Lp_iff_tendsto_eLpNorm''
    (fun j => wordDerivative X I (v j)) hj g (Lp.memLp g)).mp
  simpa only [Lp.toLp_coeFn] using hg

end RothschildStein.H3

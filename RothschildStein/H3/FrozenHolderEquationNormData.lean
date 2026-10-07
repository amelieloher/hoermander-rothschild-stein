-- Copyright (c) 2026 Scott Armstrong and Amélie Loher. All rights reserved.
-- Released under Apache 2.0 license as described in the file LICENSE.
module

public import RothschildStein.H3.LocalFirstHolderMonotonicity
public import RothschildStein.H3.FrozenDriftEquationBridge
public import RothschildStein.S.IntrinsicWeakHolderExport
public import RothschildStein.S.WeakHolderRepresentatives

set_option autoImplicit false
set_option relaxedAutoImplicit false
@[expose] public section
noncomputable section
open Set MeasureTheory TopologicalSpace
open scoped ENNReal
namespace RothschildStein.H3

/-- Fixed local order-two Hölder membership and the actual
fixed equation imply finite input and forcing suprema and a finite full
first-order norm. The forcing's L infinity property is derived. -/
theorem frozen_holder_equation_norm_data {N q : ℕ}
    (Ω U : Opens (Fin N → ℝ)) (G : S.DistanceGeometry Ω)
    (hU : (U : Set (Fin N → ℝ)) ⊆ Ω)
    (X : Fin (q + 1) → (Fin N → ℝ) → (Fin N → ℝ))
    (hX : ∀ i, ContDiffOn ℝ (⊤ : ℕ∞) (X i) (U : Set (Fin N → ℝ)))
    {α : ℝ} (hα : 0 < α) (u f : (Fin N → ℝ) → ℝ)
    (hu : memHolderX driftWeight X G.d U 2 α u)
    (heq : hasDistributionEquationWithDrift U X hX
      (Distribution.ofFun U u volume (⊤ : ℕ∞)) f) :
    MemLp u ⊤ (volume.restrict (U : Set (Fin N → ℝ))) ∧
      MemLp f ⊤ (volume.restrict (U : Set (Fin N → ℝ))) ∧
      holderXENorm driftWeight X G.d U 1 α u < ⊤ := by
  have hw := S.memWeakHolderX_of_memHolderX Ω U G hU driftWeight X hX 2 hα hu
  obtain ⟨jet, hzero, hj⟩ := S.exists_weakHolder_representatives driftWeight X G.d U 2 α hw
  have hj' (I : List (Fin (q + 1))) (hI : wordWeight driftWeight I ≤ 2) :=
    hj I ((S.mem_wordFamily_iff driftWeight 2 I).mpr hI)
  let D := holderJetDriftData Ω U G hU X hα u jet hj'
  have he := D.operator_ae_eq_of_frozen_equation (by simp) hX f heq
  refine ⟨?_, D.operator_memLp.ae_eq he, ?_⟩
  · exact memLp_top_of_local_holderNorm Ω U G hU hα hu.1
  · exact (local_first_holderNorm_mono_of_weak_jets Ω U U G hU (subset_refl _)
      X hX hα u jet hzero hj').2

end RothschildStein.H3

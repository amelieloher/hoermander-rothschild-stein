-- Copyright (c) 2026 Scott Armstrong and Amélie Loher. All rights reserved.
-- Released under Apache 2.0 license as described in the file LICENSE.
module

public import RothschildStein.H3.HolderJetFirstNorm
public import RothschildStein.S.Locality

set_option autoImplicit false
set_option relaxedAutoImplicit false
@[expose] public section
noncomputable section
open Set TopologicalSpace
open scoped ENNReal BigOperators
namespace RothschildStein.H3

/-- The selected local continuous weak jets compute finite
first-order fixed norms on every smaller open domain, and these norms
are monotone. This supplies boundedness of the actual iteration function. -/
theorem local_first_holderNorm_mono_of_weak_jets {N q : ℕ}
    (Ω U V : Opens (Fin N → ℝ)) (G : S.DistanceGeometry Ω)
    (hU : (U : Set (Fin N → ℝ)) ⊆ Ω) (hVU : (V : Set (Fin N → ℝ)) ⊆ U)
    (X : Fin (q + 1) → (Fin N → ℝ) → (Fin N → ℝ))
    (hX : ∀ i, ContDiffOn ℝ (⊤ : ℕ∞) (X i) (U : Set (Fin N → ℝ)))
    {α : ℝ} (hα : 0 < α) (u : (Fin N → ℝ) → ℝ)
    (jet : List (Fin (q + 1)) → (Fin N → ℝ) → ℝ)
    (hzero : jet [] = u)
    (hj : ∀ I, wordWeight driftWeight I ≤ 2 → hasWeakWordDeriv X U I u (jet I) ∧
      holderENorm G.d α (U : Set (Fin N → ℝ)) (jet I) < ⊤) :
    holderXENorm driftWeight X G.d V 1 α u ≤ holderXENorm driftWeight X G.d U 1 α u ∧
      holderXENorm driftWeight X G.d U 1 α u < ⊤ := by
  have hi (W : Opens (Fin N → ℝ)) (hWU : (W : Set (Fin N → ℝ)) ⊆ U)
      (i : Fin q) : hasIntrinsicWordDeriv X W [i.succ] u (jet [i.succ]) := by
    apply S.hasIntrinsicWordDeriv_of_continuous_weak_subwords W X
      (fun j => (hX j).mono hWU) [i.succ] u jet hzero
    · intro J hJ
      exact S.hasWeakWordDeriv_restrict X U W hWU
        (hj J ((S.wordWeight_sublist_le driftWeight hJ).trans
          (by simp [wordWeight, driftWeight]))).1
    · intro J hJ
      exact (S.continuousOn_of_holderENorm_lt_top_subset Ω G hU hα
        (hj J ((S.wordWeight_sublist_le driftWeight hJ).trans
          (by simp [wordWeight, driftWeight]))).2).mono hWU
  rw [holderXENorm_drift_one_eq X G.d V α u (fun i => jet [i.succ]) (hi V hVU),
    holderXENorm_drift_one_eq X G.d U α u (fun i => jet [i.succ]) (hi U (subset_refl _))]
  refine ⟨add_le_add (S.holderENorm_mono G.d α U u hVU)
    (Finset.sum_le_sum fun i _ => S.holderENorm_mono G.d α U (jet [i.succ]) hVU), ?_⟩
  apply ENNReal.add_lt_top.mpr
  refine ⟨?_, ENNReal.sum_lt_top.mpr (fun i _ => (hj _ (by simp [wordWeight, driftWeight])).2)⟩
  rw [← hzero]
  exact (hj [] (by simp [wordWeight])).2

end RothschildStein.H3

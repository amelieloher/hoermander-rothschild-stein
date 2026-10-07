-- Copyright (c) 2026 Scott Armstrong and Amélie Loher. All rights reserved.
-- Released under Apache 2.0 license as described in the file LICENSE.
module

public import RothschildStein.H3.CutoffContinuousIntrinsicJets
public import RothschildStein.S.IntrinsicWeakHolderExport
public import RothschildStein.S.WeakHolderRepresentatives
public import RothschildStein.S.HolderSubsetContinuity

set_option autoImplicit false
set_option relaxedAutoImplicit false
@[expose] public section
noncomputable section
open Set TopologicalSpace
namespace RothschildStein.H3

/-- A fixed local Hölder input has actual global compact
intrinsic cutoff jets. All exterior values of the input are allowed;
the normalized local representatives and their continuity are derived. -/
theorem exists_frozen_cutoff_intrinsic_jets {N m : ℕ}
    (Ω U : Opens (Fin N → ℝ)) (G : S.DistanceGeometry Ω)
    (hU : (U : Set (Fin N → ℝ)) ⊆ Ω) (w : Fin m → ℕ+)
    (X : Fin m → (Fin N → ℝ) → (Fin N → ℝ))
    (hX : ∀ i, ContDiff ℝ (⊤ : ℕ∞) (X i)) (k : ℕ)
    {α : ℝ} (hα : 0 < α) {u : (Fin N → ℝ) → ℝ}
    (hu : memHolderX w X G.d U k α u)
    (φ : TestFunction U ℝ (⊤ : ℕ∞)) :
    ∃ jet : List (Fin m) → (Fin N → ℝ) → ℝ,
      jet [] = u ∧
      (∀ I, wordWeight w I ≤ k → hasWeakWordDeriv X U I u (jet I) ∧
        holderENorm G.d α (U : Set (Fin N → ℝ)) (jet I) < ⊤) ∧
      (let J := fun I => S.leibnizWordValue X I jet φ
       J [] = (fun x => u x * φ x) ∧ ∀ I, wordWeight w I ≤ k →
        hasIntrinsicWordDeriv X ⊤ I (fun x => u x * φ x) (J I) ∧
        Continuous (J I) ∧ HasCompactSupport (J I) ∧ tsupport (J I) ⊆ tsupport φ) := by
  have hw := S.memWeakHolderX_of_memHolderX Ω U G hU w X
    (fun i => (hX i).contDiffOn) k hα hu
  obtain ⟨jet, hzero, hj⟩ := S.exists_weakHolder_representatives w X G.d U k α hw
  have hj' (I : List (Fin m)) (hI : wordWeight w I ≤ k) :=
    hj I ((S.mem_wordFamily_iff w k I).mpr hI)
  refine ⟨jet, hzero, hj', ?_⟩
  exact cutoff_continuous_intrinsic_jets U w X hX k u jet hzero
    (fun I hI => (hj' I hI).1)
    (fun I hI => S.continuousOn_of_holderENorm_lt_top_subset Ω G hU hα
      (hj' I hI).2) φ

end RothschildStein.H3

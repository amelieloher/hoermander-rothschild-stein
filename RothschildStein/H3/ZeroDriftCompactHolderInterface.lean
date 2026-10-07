-- Copyright (c) 2026 Scott Armstrong and Amélie Loher. All rights reserved.
-- Released under Apache 2.0 license as described in the file LICENSE.
module

public import RothschildStein.H3.ZeroDriftHolderInterfaces
public import RothschildStein.H3.ZeroDriftWordSums

set_option autoImplicit false
set_option relaxedAutoImplicit false
@[expose] public section
noncomputable section
open Set TopologicalSpace
open scoped ENNReal BigOperators
namespace RothschildStein.H3

/-- Transport both compact Holder estimates,
including the global seminorm and the centered support-radius bound. -/
theorem compactHolderEstimates_zero_drift {N q : ℕ}
    (G : HomogeneousGroup N) (X : Fin q → (Fin N → ℝ) → (Fin N → ℝ))
    (hX : ∀ i, ContDiff ℝ (⊤ : ℕ∞) (X i)) (νs : (Fin N → ℝ) → ℝ)
    (D : S.DistanceGeometry (⊤ : Opens (Fin N → ℝ)))
    (hD : D.d = controlDistance univ noDriftWeight X)
    (hnode : Provider.CompactHolderEstimates G driftWeight (Fin.cases 0 X)
      (fun Ω T f => hasDistributionEquationWithDrift Ω (Fin.cases 0 X)
        (fun i => (zeroDriftFields_contDiff X hX i).contDiffOn) T f) νs) :
    Provider.CompactHolderEstimates G noDriftWeight X
      (fun Ω T f => hasDistributionEquation Ω X (fun i => (hX i).contDiffOn) T f) νs := by
  have hd : controlDistance univ driftWeight (Fin.cases 0 X) =
      controlDistance univ noDriftWeight X := funext fun x => funext fun y =>
    controlDistance_zero_drift_eq univ X x y
  dsimp only [Provider.CompactHolderEstimates] at hnode ⊢
  rw [hd] at hnode
  have hcompact (α : ℝ) (ha : 0 < α) (u : (Fin N → ℝ) → ℝ)
      (hu : memHolderXCompact noDriftWeight X (controlDistance univ noDriftWeight X) ⊤ 2 α u) :
      memHolderXCompact driftWeight (Fin.cases 0 X) (controlDistance univ noDriftWeight X) ⊤ 2 α u := by
    have hcont : ContinuousOn u univ := S.continuousOn_of_holderENorm_lt_top_on_subset ⊤ D
      (subset_univ _) ha (by simpa only [hD, Opens.coe_top] using hu.1.1)
    exact ⟨(memHolderX_zero_drift_two_iff X _ ⊤ α u hcont).mpr hu.1, hu.2⟩
  constructor
  · intro α ha ha1
    obtain ⟨B, hB, hb⟩ := hnode.1 α ha ha1
    refine ⟨B, hB, ?_⟩
    intro u hu
    obtain ⟨f, hf, heq, g, hg, hn⟩ := hb u (hcompact α ha u hu)
    refine ⟨f, memHolderX_of_zero_drift X _ ⊤ 0 α f hf,
      (distributionEquation_zero_drift_iff ⊤ X _ _ _ f).mp heq,
      (fun I => g (I.map Fin.succ)), ?_, ?_⟩
    · intro I hI
      have hm : I.map Fin.succ ∈ (wordFamily (driftWeight (q := q)) 2).filter
          (fun I => wordWeight driftWeight I = 2) := by
        rcases Finset.mem_filter.mp hI with ⟨hi, hw⟩
        apply Finset.mem_filter.mpr
        rw [wordWeight_zero_drift_map]
        exact ⟨(S.mem_wordFamily_iff _ _ _).mpr
          (by rw [wordWeight_zero_drift_map]; exact (S.mem_wordFamily_iff _ _ _).mp hi), hw⟩
      exact (intrinsic_word_zero_drift_map_iff X ⊤ I u _).mp (hg _ hm)
    · exact (sum_zero_drift_weight_map_le 2 2
        (fun I => holderSeminorm (controlDistance univ noDriftWeight X) α univ (g I))).trans hn
  · intro α ha ha1 R hR
    obtain ⟨B, hB, hb⟩ := hnode.2 α ha ha1 R hR
    refine ⟨B, hB, ?_⟩
    intro z u hu hs
    obtain ⟨f, hf, heq, hn⟩ := hb z u (hcompact α ha u hu) hs
    refine ⟨f, memHolderX_of_zero_drift X _ ⊤ 0 α f hf,
      (distributionEquation_zero_drift_iff ⊤ X _ _ _ f).mp heq, ?_⟩
    have hm := sum_zero_drift_weight_map_le 2 2
      (fun I => intrinsicWordENorm (Fin.cases 0 X) (controlDistance univ noDriftWeight X) ⊤ I α u)
    simp only [intrinsicWordENorm_zero_drift_map] at hm
    exact hm.trans hn

end RothschildStein.H3

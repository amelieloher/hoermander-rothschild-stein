-- Copyright (c) 2026 Scott Armstrong and Amélie Loher. All rights reserved.
-- Released under Apache 2.0 license as described in the file LICENSE.
module

public import RothschildStein.H3.ZeroDriftIntrinsicWords
public import RothschildStein.H3.ZeroFieldIntrinsic
public import RothschildStein.H3.DriftWeightTwoCases
public import RothschildStein.S.HolderListSums

set_option autoImplicit false
set_option relaxedAutoImplicit false
@[expose] public section
noncomputable section
open Set TopologicalSpace
open scoped ENNReal
namespace RothschildStein.H3

/-- At order two, the only additional word from adding a zero drift
channel is its singleton. Its intrinsic representative is zero; all
remaining words are precisely shifted horizontal words. -/
theorem memHolderX_zero_drift_two_iff {N q : ℕ}
    (X : Fin q → (Fin N → ℝ) → (Fin N → ℝ))
    (d : (Fin N → ℝ) → (Fin N → ℝ) → ℝ≥0∞)
    (U : Opens (Fin N → ℝ)) (α : ℝ) (u : (Fin N → ℝ) → ℝ)
    (hcont : ContinuousOn u (U : Set (Fin N → ℝ))) :
    memHolderX driftWeight (Fin.cases 0 X) d U 2 α u ↔
      memHolderX noDriftWeight X d U 2 α u := by
  constructor
  · exact memHolderX_of_zero_drift X d U 2 α u
  · intro hu
    have hmap (I : List (Fin q)) (hI : wordWeight noDriftWeight I ≤ 2) :
        ∃ g, hasIntrinsicWordDeriv (Fin.cases 0 X) U (I.map Fin.succ) u g ∧
          holderENorm d α (U : Set (Fin N → ℝ)) g < ⊤ := by
      obtain ⟨g, hg, hn⟩ := hu.2 I ((S.mem_wordFamily_iff _ _ _).mpr hI)
      exact ⟨g, (intrinsic_word_zero_drift_map_iff X U I u g).mpr hg, hn⟩
    refine ⟨hu.1, ?_⟩
    intro I hI
    have hw := (S.mem_wordFamily_iff _ _ _).mp hI
    have hc : wordWeight driftWeight I = 0 ∨ wordWeight driftWeight I = 1 ∨
        wordWeight driftWeight I = 2 := by omega
    rcases hc with hz | h1 | h2
    · have he := word_eq_nil_of_weight_zero driftWeight I hz
      subst I
      simpa only [List.map_nil] using hmap [] (by simp [wordWeight])
    · obtain ⟨i, rfl⟩ := drift_word_weight_one I h1
      simpa only [List.map_cons, List.map_nil] using hmap [i] (by simp [wordWeight, noDriftWeight])
    · rcases drift_word_weight_two I h2 with rfl | ⟨i, j, rfl⟩
      · refine ⟨0, ?_, ?_⟩
        · exact ⟨u, (fun _ _ => rfl), hasIntrinsicDeriv_zero_field U u hcont⟩
        · change holderENorm d α (U : Set (Fin N → ℝ)) (fun _ => 0) < ⊤
          rw [S.holderENorm_zero_function]
          exact ENNReal.zero_lt_top
      · simpa only [List.map_cons, List.map_nil] using hmap [i, j] (by simp [wordWeight, noDriftWeight])

end RothschildStein.H3

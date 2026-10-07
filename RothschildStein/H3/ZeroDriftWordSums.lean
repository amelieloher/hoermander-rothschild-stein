-- Copyright (c) 2026 Scott Armstrong and Amélie Loher. All rights reserved.
-- Released under Apache 2.0 license as described in the file LICENSE.
module

public import RothschildStein.H3.ZeroDriftIntrinsicWords

set_option autoImplicit false
set_option relaxedAutoImplicit false
@[expose] public section
noncomputable section
open scoped ENNReal BigOperators
namespace RothschildStein.H3

/-- Shifting the horizontal letters embeds each fixed word family
into the family with an added zero drift channel. -/
theorem sum_zero_drift_map_le {q : ℕ} (k : ℕ)
    (f : List (Fin (q + 1)) → ℝ≥0∞) :
    (∑ I ∈ wordFamily (noDriftWeight (q := q)) k, f (I.map Fin.succ)) ≤
      ∑ I ∈ wordFamily (driftWeight (q := q)) k, f I := by
  classical
  have hinj : Function.Injective (List.map (Fin.succ : Fin q → Fin (q + 1))) :=
    List.map_injective_iff.mpr (Fin.succ_injective q)
  have hsub : (wordFamily (noDriftWeight (q := q)) k).image
      (List.map (Fin.succ : Fin q → Fin (q + 1))) ⊆
      wordFamily (driftWeight (q := q)) k := by
    intro I hI
    obtain ⟨J, hJ, rfl⟩ := Finset.mem_image.mp hI
    rw [S.mem_wordFamily_iff, wordWeight_zero_drift_map]
    exact (S.mem_wordFamily_iff _ _ _).mp hJ
  rw [← Finset.sum_image (fun a _ b _ h => hinj h)]
  exact Finset.sum_le_sum_of_subset_of_nonneg hsub (fun _ _ _ => zero_le)

/-- The same embedding preserves the weight filter used by the
literal fixed first- and second-order norm sums. -/
theorem sum_zero_drift_weight_map_le {q : ℕ} (k j : ℕ)
    (f : List (Fin (q + 1)) → ℝ≥0∞) :
    (∑ I ∈ (wordFamily (noDriftWeight (q := q)) k).filter
      (fun I => wordWeight noDriftWeight I = j), f (I.map Fin.succ)) ≤
      ∑ I ∈ (wordFamily (driftWeight (q := q)) k).filter
        (fun I => wordWeight driftWeight I = j), f I := by
  classical
  have hinj : Function.Injective (List.map (Fin.succ : Fin q → Fin (q + 1))) :=
    List.map_injective_iff.mpr (Fin.succ_injective q)
  have hsub : ((wordFamily (noDriftWeight (q := q)) k).filter
      (fun I => wordWeight noDriftWeight I = j)).image
        (List.map (Fin.succ : Fin q → Fin (q + 1))) ⊆
      (wordFamily (driftWeight (q := q)) k).filter
        (fun I => wordWeight driftWeight I = j) := by
    intro I hI
    obtain ⟨J, hJ, rfl⟩ := Finset.mem_image.mp hI
    rcases Finset.mem_filter.mp hJ with ⟨hm, hw⟩
    apply Finset.mem_filter.mpr
    rw [wordWeight_zero_drift_map]
    exact ⟨(S.mem_wordFamily_iff _ _ _).mpr
      (by rw [wordWeight_zero_drift_map]; exact (S.mem_wordFamily_iff _ _ _).mp hm), hw⟩
  rw [← Finset.sum_image (fun a _ b _ h => hinj h)]
  exact Finset.sum_le_sum_of_subset_of_nonneg hsub (fun _ _ _ => zero_le)

end RothschildStein.H3

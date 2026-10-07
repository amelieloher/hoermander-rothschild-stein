-- Copyright (c) 2026 Scott Armstrong and Amélie Loher. All rights reserved.
-- Released under Apache 2.0 license as described in the file LICENSE.
module

public import RothschildStein.H3.ZeroDriftControlDistance
public import RothschildStein.S.HolderBounds
public import RothschildStein.Definitions.memHolderX
public import RothschildStein.Definitions.holderXENorm
public import RothschildStein.S.Sobolev

set_option autoImplicit false
set_option relaxedAutoImplicit false
@[expose] public section
noncomputable section
open Set TopologicalSpace
open scoped ENNReal BigOperators
namespace RothschildStein.H3

/-- Horizontal words have exactly the same intrinsic representatives
after adding a zero drift channel and shifting each letter. -/
theorem intrinsic_word_zero_drift_map_iff {N q : ℕ}
    (X : Fin q → (Fin N → ℝ) → (Fin N → ℝ))
    (U : Opens (Fin N → ℝ)) (I : List (Fin q))
    (u g : (Fin N → ℝ) → ℝ) :
    hasIntrinsicWordDeriv (Fin.cases 0 X) U (I.map Fin.succ) u g ↔
      hasIntrinsicWordDeriv X U I u g := by
  induction I generalizing g with
  | nil => rfl
  | cons i I ih =>
    simp only [List.map_cons, hasIntrinsicWordDeriv, Fin.cases_succ, ih]

/-- Shifting horizontal letters preserves their fixed weight. -/
theorem wordWeight_zero_drift_map {q : ℕ} (I : List (Fin q)) :
    wordWeight driftWeight (I.map Fin.succ) = wordWeight noDriftWeight I := by
  simp only [wordWeight, List.map_map]
  congr 1

/-- The literal infimum defining the intrinsic norm is unchanged
for a shifted horizontal word. -/
theorem intrinsicWordENorm_zero_drift_map {N q : ℕ}
    (X : Fin q → (Fin N → ℝ) → (Fin N → ℝ))
    (d : (Fin N → ℝ) → (Fin N → ℝ) → ℝ≥0∞)
    (U : Opens (Fin N → ℝ)) (I : List (Fin q)) (α : ℝ)
    (u : (Fin N → ℝ) → ℝ) :
    intrinsicWordENorm (Fin.cases 0 X) d U (I.map Fin.succ) α u =
      intrinsicWordENorm X d U I α u := by
  simp only [intrinsicWordENorm, intrinsic_word_zero_drift_map_iff]

/-- The full horizontal Holder norm is bounded by the norm with
an additional zero drift channel, for every order. -/
theorem holderXENorm_le_zero_drift {N q : ℕ}
    (X : Fin q → (Fin N → ℝ) → (Fin N → ℝ))
    (d : (Fin N → ℝ) → (Fin N → ℝ) → ℝ≥0∞)
    (U : Opens (Fin N → ℝ)) (k : ℕ) (α : ℝ)
    (u : (Fin N → ℝ) → ℝ) :
    holderXENorm noDriftWeight X d U k α u ≤
      holderXENorm driftWeight (Fin.cases 0 X) d U k α u := by
  classical
  let f := fun I : List (Fin (q + 1)) => intrinsicWordENorm (Fin.cases 0 X) d U I α u
  have hinj : Function.Injective (List.map (Fin.succ : Fin q → Fin (q + 1))) :=
    List.map_injective_iff.mpr (Fin.succ_injective q)
  have hsub : (wordFamily (noDriftWeight (q := q)) k).image
      (List.map (Fin.succ : Fin q → Fin (q + 1))) ⊆
      wordFamily (driftWeight (q := q)) k := by
    intro I hI
    obtain ⟨J, hJ, rfl⟩ := Finset.mem_image.mp hI
    rw [S.mem_wordFamily_iff, wordWeight_zero_drift_map]
    exact (S.mem_wordFamily_iff _ _ _).mp hJ
  unfold holderXENorm
  calc
    _ = ∑ I ∈ (wordFamily (noDriftWeight (q := q)) k).image
        (List.map (Fin.succ : Fin q → Fin (q + 1))), f I := by
      rw [Finset.sum_image (fun a _ b _ h => hinj h)]
      simp only [f, intrinsicWordENorm_zero_drift_map]
    _ ≤ _ := Finset.sum_le_sum_of_subset_of_nonneg hsub (fun _ _ _ => zero_le)

/-- Membership with the zero drift channel restricts to all horizontal
words, without any auxiliary analytic premise. -/
theorem memHolderX_of_zero_drift {N q : ℕ}
    (X : Fin q → (Fin N → ℝ) → (Fin N → ℝ))
    (d : (Fin N → ℝ) → (Fin N → ℝ) → ℝ≥0∞)
    (U : Opens (Fin N → ℝ)) (k : ℕ) (α : ℝ)
    (u : (Fin N → ℝ) → ℝ)
    (hu : memHolderX driftWeight (Fin.cases 0 X) d U k α u) :
    memHolderX noDriftWeight X d U k α u := by
  refine ⟨hu.1, ?_⟩
  intro I hI
  have hm : I.map Fin.succ ∈ wordFamily driftWeight k := by
    rw [S.mem_wordFamily_iff, wordWeight_zero_drift_map]
    exact (S.mem_wordFamily_iff _ _ _).mp hI
  obtain ⟨g, hg, hn⟩ := hu.2 _ hm
  exact ⟨g, (intrinsic_word_zero_drift_map_iff X U I u g).mp hg, hn⟩

end RothschildStein.H3

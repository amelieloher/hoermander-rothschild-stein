-- Copyright (c) 2026 Scott Armstrong and Amélie Loher. All rights reserved.
-- Released under Apache 2.0 license as described in the file LICENSE.
module

public import RothschildStein.H3.ZeroDriftWordSums
public import RothschildStein.H3.ZeroFieldIntrinsic
public import RothschildStein.H3.DriftWeightTwoCases
public import RothschildStein.Definitions.sobolevXENorm

set_option autoImplicit false
set_option relaxedAutoImplicit false
@[expose] public section
noncomputable section
open Set TopologicalSpace MeasureTheory
open scoped ENNReal BigOperators
namespace RothschildStein.H3

/-- The literal weak transpose of a shifted horizontal word is unchanged. -/
theorem wordTranspose_zero_drift_map {N q : ℕ}
    (X : Fin q → (Fin N → ℝ) → (Fin N → ℝ)) (I : List (Fin q))
    (φ : (Fin N → ℝ) → ℝ) :
    wordTranspose (Fin.cases 0 X) (I.map Fin.succ) φ = wordTranspose X I φ := by
  induction I generalizing φ with
  | nil => rfl
  | cons i I ih => simp only [List.map_cons, wordTranspose, Fin.cases_succ, ih]

/-- Horizontal weak representatives are preserved by the zero drift transport. -/
theorem weak_word_zero_drift_map_iff {N q : ℕ}
    (X : Fin q → (Fin N → ℝ) → (Fin N → ℝ)) (U : Opens (Fin N → ℝ))
    (I : List (Fin q)) (u g : (Fin N → ℝ) → ℝ) :
    hasWeakWordDeriv (Fin.cases 0 X) U (I.map Fin.succ) u g ↔
      hasWeakWordDeriv X U I u g := by
  simp only [hasWeakWordDeriv, wordTranspose_zero_drift_map]

/-- The exact infimum defining a horizontal weak norm is unchanged. -/
theorem weakWordENorm_zero_drift_map {N q : ℕ}
    (X : Fin q → (Fin N → ℝ) → (Fin N → ℝ)) (U : Opens (Fin N → ℝ))
    (I : List (Fin q)) (p : ℝ≥0∞) (u : (Fin N → ℝ) → ℝ) :
    weakWordENorm (Fin.cases 0 X) U (I.map Fin.succ) p u =
      weakWordENorm X U I p u := by
  simp only [weakWordENorm, weak_word_zero_drift_map_iff]

/-- The exact full horizontal Sobolev norm is bounded by the norm
with the additional zero drift channel. -/
theorem sobolevXENorm_le_zero_drift {N q : ℕ}
    (X : Fin q → (Fin N → ℝ) → (Fin N → ℝ)) (U : Opens (Fin N → ℝ))
    (k : ℕ) (p : ℝ≥0∞) (u : (Fin N → ℝ) → ℝ) :
    sobolevXENorm noDriftWeight X U k p u ≤
      sobolevXENorm driftWeight (Fin.cases 0 X) U k p u := by
  unfold sobolevXENorm
  simpa only [weakWordENorm_zero_drift_map] using
    sum_zero_drift_map_le k (fun I => weakWordENorm (Fin.cases 0 X) U I p u)

/-- Membership in the extended Sobolev class implies membership in
the horizontal class, for every order and exponent. -/
theorem memSobolevX_of_zero_drift {N q : ℕ}
    (X : Fin q → (Fin N → ℝ) → (Fin N → ℝ)) (U : Opens (Fin N → ℝ))
    (k : ℕ) (p : ℝ≥0∞) (u : (Fin N → ℝ) → ℝ)
    (hu : memSobolevX driftWeight (Fin.cases 0 X) U k p u) :
    memSobolevX noDriftWeight X U k p u := by
  refine ⟨hu.1, ?_⟩
  intro I hI
  have hm : I.map Fin.succ ∈ wordFamily driftWeight k := by
    rw [S.mem_wordFamily_iff, wordWeight_zero_drift_map]
    exact (S.mem_wordFamily_iff _ _ _).mp hI
  obtain ⟨g, hg, hn⟩ := hu.2 _ hm
  exact ⟨g, (weak_word_zero_drift_map_iff X U I u g).mp hg, hn⟩

/-- Each fixed filtered horizontal weak norm sum is bounded by the
corresponding sum for the extended frame. -/
theorem weakWordWeightSum_le_zero_drift {N q : ℕ}
    (X : Fin q → (Fin N → ℝ) → (Fin N → ℝ)) (U : Opens (Fin N → ℝ))
    (k j : ℕ) (p : ℝ≥0∞) (u : (Fin N → ℝ) → ℝ) :
    (∑ I ∈ (wordFamily (noDriftWeight (q := q)) k).filter
      (fun I => wordWeight noDriftWeight I = j), weakWordENorm X U I p u) ≤
      ∑ I ∈ (wordFamily (driftWeight (q := q)) k).filter
        (fun I => wordWeight driftWeight I = j), weakWordENorm (Fin.cases 0 X) U I p u := by
  simpa only [weakWordENorm_zero_drift_map] using
    sum_zero_drift_weight_map_le k j (fun I => weakWordENorm (Fin.cases 0 X) U I p u)

/-- At order two the additional drift singleton has zero weak
representative, so the two literal Sobolev membership predicates agree. -/
theorem memSobolevX_zero_drift_two_iff {N q : ℕ}
    (X : Fin q → (Fin N → ℝ) → (Fin N → ℝ)) (U : Opens (Fin N → ℝ))
    (p : ℝ≥0∞) (u : (Fin N → ℝ) → ℝ) :
    memSobolevX driftWeight (Fin.cases 0 X) U 2 p u ↔
      memSobolevX noDriftWeight X U 2 p u := by
  constructor
  · exact memSobolevX_of_zero_drift X U 2 p u
  · intro hu
    have hmap (I : List (Fin q)) (hI : wordWeight noDriftWeight I ≤ 2) :
        ∃ g, hasWeakWordDeriv (Fin.cases 0 X) U (I.map Fin.succ) u g ∧
          MemLp g p (volume.restrict (U : Set (Fin N → ℝ))) := by
      obtain ⟨g, hg, hn⟩ := hu.2 I ((S.mem_wordFamily_iff _ _ _).mpr hI)
      exact ⟨g, (weak_word_zero_drift_map_iff X U I u g).mpr hg, hn⟩
    have hLI : LocallyIntegrableOn u (U : Set (Fin N → ℝ)) volume :=
      (hu.2 [] (S.nil_mem_wordFamily noDriftWeight 2)).choose_spec.1.1
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
      · refine ⟨0, ⟨hLI, continuousOn_const.locallyIntegrableOn U.isOpen.measurableSet, ?_⟩, MemLp.zero⟩
        intro φ
        simp [wordTranspose, fieldTranspose_zero_field]
      · simpa only [List.map_cons, List.map_nil] using hmap [i, j] (by simp [wordWeight, noDriftWeight])

end RothschildStein.H3

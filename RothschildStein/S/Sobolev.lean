-- Copyright (c) 2026 Scott Armstrong and Amélie Loher. All rights reserved.
-- Released under Apache 2.0 license as described in the file LICENSE.
module

public import RothschildStein.S.WeakDeriv
public import RothschildStein.Definitions.memSobolevXLoc
public import RothschildStein.Definitions.memSobolevXZero

set_option autoImplicit false
set_option relaxedAutoImplicit false

@[expose] public section
noncomputable section
open Set MeasureTheory TopologicalSpace Filter
open scoped BigOperators Topology ENNReal
namespace RothschildStein.S
variable {m n : ℕ}

/-- Every letter has positive weight, so weight bounds ordinary length
(BB Def. 1.17, p. 10; Def. 2.2, p. 68). -/
theorem length_le_wordWeight (w : Fin m → ℕ+) (I : List (Fin m)) :
    I.length ≤ wordWeight w I := by
  induction I with
  | nil => simp [wordWeight]
  | cons i I ih =>
    have hi := (w i).pos
    simp only [wordWeight, List.map_cons, List.sum_cons, List.length_cons] at *
    omega

/-- The finite family contains exactly words of weight at most k
(BB Def. 2.2, p. 68). -/
theorem mem_wordFamily_iff (w : Fin m → ℕ+) (k : ℕ) (I : List (Fin m)) :
    I ∈ wordFamily w k ↔ wordWeight w I ≤ k := by
  classical
  unfold wordFamily
  rw [Finset.mem_filter]
  refine ⟨fun h => h.2, fun h => ⟨?_, h⟩⟩
  apply Finset.mem_biUnion.mpr
  refine ⟨I.length, Finset.mem_range.mpr (by have := length_le_wordWeight w I; omega), ?_⟩
  apply Finset.mem_image.mpr
  exact ⟨fun i => I.get i, Finset.mem_univ _, by simp⟩

/-- The empty word belongs to every weighted family (BB p. 68). -/
theorem nil_mem_wordFamily (w : Fin m → ℕ+) (k : ℕ) : [] ∈ wordFamily w k := by
  simp [mem_wordFamily_iff, wordWeight]

/-- Raising the derivative order only strengthens Sobolev membership
(BB Def. 2.2, p. 68). -/
theorem memSobolevX_mono_order (w : Fin m → ℕ+)
    (X : Fin m → (Fin n → ℝ) → (Fin n → ℝ)) (Ω : Opens (Fin n → ℝ))
    {k l : ℕ} {p : ℝ≥0∞} {f : (Fin n → ℝ) → ℝ}
    (hkl : k ≤ l) (hf : memSobolevX w X Ω l p f) : memSobolevX w X Ω k p f := by
  refine ⟨hf.1, fun I hI => hf.2 I ?_⟩
  exact (mem_wordFamily_iff w l I).mpr (((mem_wordFamily_iff w k I).mp hI).trans hkl)

/-- Order zero is exactly Lᵖ for the stated range p ≥ 1 (BB p. 68). -/
theorem memSobolevX_zero_iff (w : Fin m → ℕ+)
    (X : Fin m → (Fin n → ℝ) → (Fin n → ℝ)) (Ω : Opens (Fin n → ℝ))
    (p : ℝ≥0∞) (hp : 1 ≤ p) (f : (Fin n → ℝ) → ℝ) :
    memSobolevX w X Ω 0 p f ↔ MemLp f p (volume.restrict (Ω : Set (Fin n → ℝ))) := by
  refine ⟨fun h => h.1, fun h => ⟨h, fun I hI => ?_⟩⟩
  have hw := (mem_wordFamily_iff w 0 I).mp hI
  have hl := length_le_wordWeight w I
  have he : I = [] := List.length_eq_zero_iff.mp (by omega)
  subst I
  exact ⟨f, hasWeakWordDeriv_nil X Ω
    (locallyIntegrableOn_of_locallyIntegrable_restrict (h.locallyIntegrable hp)), h⟩

/-- Sobolev membership restricts to smaller open sets (BB p. 535). -/
theorem memSobolevX_restrict (w : Fin m → ℕ+)
    (X : Fin m → (Fin n → ℝ) → (Fin n → ℝ)) (Ω U : Opens (Fin n → ℝ))
    (hU : (U : Set (Fin n → ℝ)) ⊆ (Ω : Set (Fin n → ℝ)))
    {k : ℕ} {p : ℝ≥0∞} {f : (Fin n → ℝ) → ℝ}
    (h : memSobolevX w X Ω k p f) : memSobolevX w X U k p f := by
  have hμ : volume.restrict (U : Set (Fin n → ℝ)) ≤
      volume.restrict (Ω : Set (Fin n → ℝ)) := Measure.restrict_mono hU le_rfl
  refine ⟨h.1.mono_measure hμ, fun I hI => ?_⟩
  obtain ⟨g, hg, hgp⟩ := h.2 I hI
  exact ⟨g, hasWeakWordDeriv_restrict X Ω U hU hg, hgp.mono_measure hμ⟩

/-- The infimum norm equals the norm of any weak representative
(BB Def. 2.2, p. 68; uniqueness). -/
theorem weakWordENorm_eq (X : Fin m → (Fin n → ℝ) → (Fin n → ℝ))
    (Ω : Opens (Fin n → ℝ)) (I : List (Fin m)) (p : ℝ≥0∞)
    (f g : (Fin n → ℝ) → ℝ) (hg : hasWeakWordDeriv X Ω I f g) :
    weakWordENorm X Ω I p f = eLpNorm g p (volume.restrict (Ω : Set (Fin n → ℝ))) := by
  unfold weakWordENorm
  have he : {r | ∃ h : (Fin n → ℝ) → ℝ,
      hasWeakWordDeriv X Ω I f h ∧
      AEStronglyMeasurable h (volume.restrict (Ω : Set (Fin n → ℝ))) ∧
      r = eLpNorm h p (volume.restrict (Ω : Set (Fin n → ℝ)))} =
      {eLpNorm g p (volume.restrict (Ω : Set (Fin n → ℝ)))} := by
    ext r
    constructor
    · rintro ⟨h, hh, _, rfl⟩
      exact Set.mem_singleton_iff.mpr
        (eLpNorm_congr_ae (hasWeakWordDeriv_unique X Ω hh hg))
    · intro hr
      exact ⟨g, hg, hg.2.1.aestronglyMeasurable, Set.mem_singleton_iff.mp hr⟩
  rw [he, sInf_singleton]

/-- Deleting letters lowers weight (BB Def. 2.2, p. 68). -/
theorem wordWeight_sublist_le (w : Fin m → ℕ+) {I J : List (Fin m)}
    (h : List.Sublist I J) : wordWeight w I ≤ wordWeight w J := by
  induction h with
  | slnil => simp [wordWeight]
  | cons i h ih =>
    simp only [wordWeight, List.map_cons, List.sum_cons] at *
    omega
  | cons_cons i h ih =>
    simp only [wordWeight, List.map_cons, List.sum_cons] at *
    omega

/-- Weighted Sobolev words form a subword-closed family (BB p. 68). -/
theorem sublist_mem_wordFamily (w : Fin m → ℕ+) (k : ℕ) {I J : List (Fin m)}
    (h : List.Sublist I J) (hJ : J ∈ wordFamily w k) : I ∈ wordFamily w k := by
  rw [mem_wordFamily_iff] at hJ ⊢
  exact (wordWeight_sublist_le w h).trans hJ

end RothschildStein.S

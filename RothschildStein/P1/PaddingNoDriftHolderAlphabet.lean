-- Copyright (c) 2026 Scott Armstrong and Amélie Loher. All rights reserved.
-- Released under Apache 2.0 license as described in the file LICENSE.
module

public import RothschildStein.P1.PaddingNoDriftBaseAlphabet
public import RothschildStein.P1.IntrinsicWordReindex
public import RothschildStein.P1.IntrinsicZeroFunction
public import RothschildStein.P1.ZeroFieldIntrinsicWords
public import RothschildStein.S.HolderListSums
public import RothschildStein.Definitions.memHolderX

set_option autoImplicit false
set_option relaxedAutoImplicit false
set_option backward.isDefEq.respectTransparency false
@[expose] public section
noncomputable section
open Set TopologicalSpace
open scoped ENNReal
namespace RothschildStein.P1

private theorem holderAlphabet_original_family {q n d : ℕ}
    (X : Fin q → (Fin n → ℝ) → (Fin n → ℝ)) :
    paddingNoDriftBaseAlphabet (d := d) X ∘ Fin.castAdd d = X := by
  funext i
  simp [paddingNoDriftBaseAlphabet]

private theorem holderAlphabet_smooth {q n d : ℕ}
    (Ω : Opens (Fin n → ℝ)) (X : Fin q → (Fin n → ℝ) → (Fin n → ℝ))
    (hX : ∀ i, ContDiffOn ℝ (⊤ : ℕ∞) (X i) (Ω : Set (Fin n → ℝ))) :
    ∀ i, ContDiffOn ℝ (⊤ : ℕ∞) (paddingNoDriftBaseAlphabet (d := d) X i)
      (Ω : Set (Fin n → ℝ)) := by
  intro i
  refine Fin.addCases (fun a => ?_) (fun b => ?_) i
  · simpa [paddingNoDriftBaseAlphabet] using hX a
  · simp only [paddingNoDriftBaseAlphabet, Fin.addCases_right]
    simpa only [Pi.zero_def] using
      (contDiff_zero_fun (𝕜 := ℝ) (n := (⊤ : ℕ∞))
        (E := Fin n → ℝ) (F := Fin n → ℝ)).contDiffOn

/-- Intrinsic derivatives of words containing an appended index
vanish in the projected padded alphabet, at every weighted order. -/
theorem hasIntrinsicWordDeriv_paddingNoDriftBaseAlphabet_added {q n d k : ℕ}
    (Ω : Opens (Fin n → ℝ)) (w : Fin q → ℕ+)
    (X : Fin q → (Fin n → ℝ) → (Fin n → ℝ))
    (hX : ∀ i, ContDiffOn ℝ (⊤ : ℕ∞) (X i) (Ω : Set (Fin n → ℝ)))
    (D : (Fin n → ℝ) → (Fin n → ℝ) → ℝ≥0∞) (α : ℝ)
    (f : (Fin n → ℝ) → ℝ) (hf : memHolderX w X D Ω k α f)
    (I : List (Fin (q + d)))
    (hI : I ∈ wordFamily (paddingNoDriftWeights (d := d) w) k)
    (j : Fin d) (hj : Fin.natAdd q j ∈ I) :
    hasIntrinsicWordDeriv (paddingNoDriftBaseAlphabet (d := d) X) Ω I f (fun _ => 0) := by
  induction I generalizing j with
  | nil => simp at hj
  | cons i I ih =>
    have htail : I ∈ wordFamily (paddingNoDriftWeights (d := d) w) k := by
      apply (S.mem_wordFamily_iff _ _ _).mpr
      have h := (S.mem_wordFamily_iff _ _ _).mp hI
      simp only [wordWeight, List.map_cons, List.sum_cons] at h ⊢
      omega
    rcases List.mem_cons.mp hj with he | hj
    · subst i
      have hinner : ∃ g, hasIntrinsicWordDeriv (paddingNoDriftBaseAlphabet (d := d) X) Ω I f g := by
        rcases padding_word_original_or_added I with ⟨L, rfl⟩ | ⟨l, hl⟩
        · have hL : L ∈ wordFamily w k := by
            apply (S.mem_wordFamily_iff _ _ _).mpr
            have h := (S.mem_wordFamily_iff _ _ _).mp htail
            rwa [wordWeight_paddingNoDrift_map] at h
          obtain ⟨g, hg, _⟩ := hf.2 L hL
          refine ⟨g, (hasIntrinsicWordDeriv_map_indices_iff _ _ _ _ _ _).mpr ?_⟩
          rw [holderAlphabet_original_family]
          exact hg
        · exact ⟨fun _ => 0, ih htail l hl⟩
      obtain ⟨g, hg⟩ := hinner
      refine ⟨g, hg, ?_⟩
      simpa only [paddingNoDriftBaseAlphabet, Fin.addCases_right, Pi.zero_def] using
        hasIntrinsicDeriv_zero_field Ω g
    · exact ⟨fun _ => 0, ih htail j hj,
        hasIntrinsicDeriv_zero_function Ω _ (holderAlphabet_smooth Ω X hX i)⟩

/-- Pointwise intrinsic Hölder regularity at every order
transfers to the projected padded alphabet. Every word with an added
index has zero derivative; the empty word remains pointwise. -/
theorem memHolderX_paddingNoDriftBaseAlphabet {q n d k : ℕ}
    (Ω : Opens (Fin n → ℝ)) (w : Fin q → ℕ+)
    (X : Fin q → (Fin n → ℝ) → (Fin n → ℝ))
    (hX : ∀ i, ContDiffOn ℝ (⊤ : ℕ∞) (X i) (Ω : Set (Fin n → ℝ)))
    (D : (Fin n → ℝ) → (Fin n → ℝ) → ℝ≥0∞) (α : ℝ)
    (f : (Fin n → ℝ) → ℝ) (hf : memHolderX w X D Ω k α f) :
    memHolderX (paddingNoDriftWeights (d := d) w)
      (paddingNoDriftBaseAlphabet (d := d) X) D Ω k α f := by
  refine ⟨hf.1, ?_⟩
  intro I hI
  rcases padding_word_original_or_added I with ⟨L, rfl⟩ | ⟨j, hj⟩
  · have hL : L ∈ wordFamily w k := by
      apply (S.mem_wordFamily_iff _ _ _).mpr
      have h := (S.mem_wordFamily_iff _ _ _).mp hI
      rwa [wordWeight_paddingNoDrift_map] at h
    obtain ⟨g, hg, hgn⟩ := hf.2 L hL
    refine ⟨g, (hasIntrinsicWordDeriv_map_indices_iff _ _ _ _ _ _).mpr ?_, hgn⟩
    rw [holderAlphabet_original_family]
    exact hg
  · exact ⟨fun _ => 0, hasIntrinsicWordDeriv_paddingNoDriftBaseAlphabet_added Ω w X hX D α f hf I hI j hj,
      by rw [S.holderENorm_zero_function]; exact ENNReal.zero_lt_top⟩

end RothschildStein.P1

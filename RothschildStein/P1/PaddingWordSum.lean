-- Copyright (c) 2026 Scott Armstrong and Amélie Loher. All rights reserved.
-- Released under Apache 2.0 license as described in the file LICENSE.
module

public import RothschildStein.P1.PaddingAlphabetWords
public import RothschildStein.P1.PaddingDriftAlphabetWords
public import RothschildStein.P1.PaddingIndexEmbedding
public import RothschildStein.S.Sobolev

set_option autoImplicit false
set_option relaxedAutoImplicit false
@[expose] public section
noncomputable section
open scoped BigOperators ENNReal
namespace RothschildStein.P1

private theorem wordFamily_sum_map {a b : ℕ} (w : Fin a → ℕ+) (W : Fin b → ℕ+)
    (e : Fin a → Fin b) (he : Function.Injective e)
    (hw : ∀ I, wordWeight W (I.map e) = wordWeight w I)
    (k : ℕ) (F : List (Fin b) → ℝ≥0∞)
    (hz : ∀ I ∈ wordFamily W k, (∀ L : List (Fin a), I ≠ L.map e) → F I = 0) :
    (∑ I ∈ wordFamily W k, F I) = ∑ I ∈ wordFamily w k, F (I.map e) := by
  classical
  have hinj := List.map_injective_iff.mpr he
  have hsub : (wordFamily w k).image (List.map e) ⊆ wordFamily W k := by
    intro I hI
    obtain ⟨L, hL, rfl⟩ := Finset.mem_image.mp hI
    apply (S.mem_wordFamily_iff _ _ _).mpr
    rw [hw]
    exact (S.mem_wordFamily_iff _ _ _).mp hL
  have hsum : (∑ I ∈ (wordFamily w k).image (List.map e), F I) =
      ∑ I ∈ wordFamily w k, F (I.map e) :=
    Finset.sum_image (fun _ _ _ _ h => hinj h)
  rw [← hsum]
  symm
  apply Finset.sum_subset hsub
  intro I hI hn
  apply hz I hI
  intro L heq
  apply hn
  apply Finset.mem_image.mpr
  refine ⟨L, ?_, heq.symm⟩
  apply (S.mem_wordFamily_iff _ _ _).mpr
  have h := (S.mem_wordFamily_iff _ _ _).mp hI
  rw [heq, hw] at h
  exact h

/-- Summing over the full padded no-drift word family reduces
exactly to the original word sum when all added-index terms vanish. -/
theorem sum_paddingNoDrift_wordFamily {q d k : ℕ} (w : Fin q → ℕ+)
    (F : List (Fin (q + d)) → ℝ≥0∞)
    (hz : ∀ I ∈ wordFamily (paddingNoDriftWeights (d := d) w) k,
      ∀ j : Fin d, Fin.natAdd q j ∈ I → F I = 0) :
    (∑ I ∈ wordFamily (paddingNoDriftWeights (d := d) w) k, F I) =
      ∑ I ∈ wordFamily w k, F (I.map (Fin.castAdd d)) := by
  apply wordFamily_sum_map w _ _ (Fin.castAdd_injective _ _) (wordWeight_paddingNoDrift_map w) k F
  intro I hI hn
  rcases padding_word_original_or_added I with ⟨L, he⟩ | ⟨j, hj⟩
  · exact False.elim (hn L he)
  · exact hz I hI j hj

/-- The analogous exact word-sum reduction preserves the
original drift index and the drift weight. -/
theorem sum_paddingDrift_wordFamily {q d k : ℕ} (w : Fin (q + 1) → ℕ+)
    (F : List (Fin (q + d + 1)) → ℝ≥0∞)
    (hz : ∀ I ∈ wordFamily (paddingControlWeights (d := d) w) k,
      ∀ j : Fin d, (Fin.natAdd q j).succ ∈ I → F I = 0) :
    (∑ I ∈ wordFamily (paddingControlWeights (d := d) w) k, F I) =
      ∑ I ∈ wordFamily w k, F (I.map paddingGeneratorIndex) := by
  apply wordFamily_sum_map w _ _ paddingGeneratorIndex_injective (wordWeight_padding_map w) k F
  intro I hI hn
  rcases padding_drift_word_original_or_added I with ⟨L, he⟩ | ⟨j, hj⟩
  · exact False.elim (hn L he)
  · exact hz I hI j hj

end RothschildStein.P1

-- Copyright (c) 2026 Scott Armstrong and Amélie Loher. All rights reserved.
-- Released under Apache 2.0 license as described in the file LICENSE.
module

public import RothschildStein.P1.PaddingDriftAlphabetWords
public import RothschildStein.P1.ZeroFieldWeakWords
public import RothschildStein.P1.WordReindex
public import RothschildStein.Definitions.memSobolevX
public import RothschildStein.S.Sobolev

set_option autoImplicit false
set_option relaxedAutoImplicit false
set_option backward.isDefEq.respectTransparency false
@[expose] public section
noncomputable section
open Set MeasureTheory TopologicalSpace
open scoped ENNReal
namespace RothschildStein.P1

/-- Base projection of the genuine drift-padded family.
Added diffusions project to zero. This family is only a function-space
adapter and is never used as a free model. -/
def paddingDriftBaseAlphabet {q n d : ℕ}
    (X : Fin (q + 1) → (Fin n → ℝ) → (Fin n → ℝ)) :
    Fin (q + d + 1) → (Fin n → ℝ) → (Fin n → ℝ) :=
  Fin.cases (X 0) (Fin.addCases (fun j => X j.succ) (fun _ => 0))

/-- Every Sobolev order of the forcing transfers to the
projected drift-padded alphabet, including all words with added indices. -/
theorem memSobolevX_paddingDriftBaseAlphabet {q n d k : ℕ}
    (Ω : Opens (Fin n → ℝ)) (w : Fin (q + 1) → ℕ+)
    (X : Fin (q + 1) → (Fin n → ℝ) → (Fin n → ℝ))
    (p : ℝ≥0∞) (f : (Fin n → ℝ) → ℝ)
    (hf : memSobolevX w X Ω k p f) :
    memSobolevX (paddingControlWeights (d := d) w)
      (paddingDriftBaseAlphabet (d := d) X) Ω k p f := by
  have hnil : ([] : List (Fin (q + 1))) ∈ wordFamily w k := by
    apply (S.mem_wordFamily_iff _ _ _).mpr
    simp [wordWeight]
  obtain ⟨g₀, hg₀, _⟩ := hf.2 [] hnil
  refine ⟨hf.1, ?_⟩
  intro I hI
  rcases padding_drift_word_original_or_added I with ⟨L, rfl⟩ | ⟨j, hj⟩
  · have hL : L ∈ wordFamily w k := by
      apply (S.mem_wordFamily_iff _ _ _).mpr
      have h := (S.mem_wordFamily_iff _ _ _).mp hI
      rwa [wordWeight_padding_map] at h
    obtain ⟨g, hg, hgp⟩ := hf.2 L hL
    refine ⟨g, ?_, hgp⟩
    apply (hasWeakWordDeriv_map_indices_iff _ _ _ _ _ _).mpr
    have he : paddingDriftBaseAlphabet (d := d) X ∘ paddingGeneratorIndex (d := d) = X := by
      funext i
      refine Fin.cases (by simp [paddingDriftBaseAlphabet, paddingGeneratorIndex])
        (fun j => by simp [paddingDriftBaseAlphabet, paddingGeneratorIndex]) i
    rw [he]
    exact hg
  · refine ⟨fun _ => 0, ?_, MemLp.zero'⟩
    apply hasWeakWordDeriv_zero_of_zero_field_mem _ Ω I (Fin.natAdd q j).succ hj _ f hg₀.1
    simp [paddingDriftBaseAlphabet]

end RothschildStein.P1

-- Copyright (c) 2026 Scott Armstrong and Amélie Loher. All rights reserved.
-- Released under Apache 2.0 license as described in the file LICENSE.
module

public import RothschildStein.P1.PaddingAlphabetWords
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

/-- Base projection of the genuine padded diffusion family.
Added diffusions project to zero. This family is only a function-space
adapter and is never used as a free model. -/
def paddingNoDriftBaseAlphabet {q n d : ℕ}
    (X : Fin q → (Fin n → ℝ) → (Fin n → ℝ)) :
    Fin (q + d) → (Fin n → ℝ) → (Fin n → ℝ) :=
  Fin.addCases X (fun _ => 0)

/-- Every Sobolev order of the forcing transfers to the
projected padded alphabet, including all words with added indices. -/
theorem memSobolevX_paddingNoDriftBaseAlphabet {q n d k : ℕ}
    (Ω : Opens (Fin n → ℝ)) (w : Fin q → ℕ+)
    (X : Fin q → (Fin n → ℝ) → (Fin n → ℝ))
    (p : ℝ≥0∞) (f : (Fin n → ℝ) → ℝ)
    (hf : memSobolevX w X Ω k p f) :
    memSobolevX (paddingNoDriftWeights (d := d) w)
      (paddingNoDriftBaseAlphabet (d := d) X) Ω k p f := by
  have hnil : ([] : List (Fin q)) ∈ wordFamily w k := by
    apply (S.mem_wordFamily_iff _ _ _).mpr
    simp [wordWeight]
  obtain ⟨g₀, hg₀, _⟩ := hf.2 [] hnil
  refine ⟨hf.1, ?_⟩
  intro I hI
  rcases padding_word_original_or_added I with ⟨L, rfl⟩ | ⟨j, hj⟩
  · have hL : L ∈ wordFamily w k := by
      apply (S.mem_wordFamily_iff _ _ _).mpr
      have h := (S.mem_wordFamily_iff _ _ _).mp hI
      rwa [wordWeight_paddingNoDrift_map] at h
    obtain ⟨g, hg, hgp⟩ := hf.2 L hL
    refine ⟨g, ?_, hgp⟩
    apply (hasWeakWordDeriv_map_indices_iff _ _ _ _ _ _).mpr
    have he : paddingNoDriftBaseAlphabet (d := d) X ∘ Fin.castAdd d = X := by
      funext i
      simp [paddingNoDriftBaseAlphabet]
    rw [he]
    exact hg
  · refine ⟨fun _ => 0, ?_, MemLp.zero'⟩
    apply hasWeakWordDeriv_zero_of_zero_field_mem _ Ω I (Fin.natAdd q j) hj _ f hg₀.1
    simp [paddingNoDriftBaseAlphabet]

end RothschildStein.P1

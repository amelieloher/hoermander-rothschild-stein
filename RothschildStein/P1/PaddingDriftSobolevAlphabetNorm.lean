-- Copyright (c) 2026 Scott Armstrong and Amélie Loher. All rights reserved.
-- Released under Apache 2.0 license as described in the file LICENSE.
module

public import RothschildStein.P1.PaddingDriftBaseAlphabet
public import RothschildStein.P1.PaddingWordSum
public import RothschildStein.Definitions.sobolevXENorm

set_option autoImplicit false
set_option relaxedAutoImplicit false
set_option backward.isDefEq.respectTransparency false
@[expose] public section
noncomputable section
open Set MeasureTheory TopologicalSpace
open scoped ENNReal BigOperators
namespace RothschildStein.P1

/-- The Sobolev norm is unchanged by the projected
padded alphabet: original words retain their infimum norms, and every
added-index word contributes zero. Infinite values are included. -/
theorem sobolevXENorm_paddingDriftBaseAlphabet_eq {q n d k : ℕ}
    (Ω : Opens (Fin n → ℝ)) (w : Fin (q + 1) → ℕ+)
    (X : Fin (q + 1) → (Fin n → ℝ) → (Fin n → ℝ))
    (p : ℝ≥0∞) (f : (Fin n → ℝ) → ℝ)
    (hf : LocallyIntegrableOn f (Ω : Set (Fin n → ℝ)) volume) :
    sobolevXENorm (paddingControlWeights (d := d) w) (paddingDriftBaseAlphabet (d := d) X) Ω k p f =
      sobolevXENorm w X Ω k p f := by
  have he : paddingDriftBaseAlphabet (d := d) X ∘ paddingGeneratorIndex = X := by
    funext i
    refine Fin.cases (by simp [paddingDriftBaseAlphabet, paddingGeneratorIndex])
      (fun j => by simp [paddingDriftBaseAlphabet, paddingGeneratorIndex]) i
  have hword (I : List (Fin (q + 1))) :
      weakWordENorm (paddingDriftBaseAlphabet (d := d) X) Ω (I.map paddingGeneratorIndex) p f = weakWordENorm X Ω I p f := by
    simp only [weakWordENorm, hasWeakWordDeriv_map_indices_iff, he]
  have hzero (I : List (Fin (q + d + 1)))
      (_ : I ∈ wordFamily (paddingControlWeights (d := d) w) k)
      (j : Fin d) (hj : (Fin.natAdd q j).succ ∈ I) :
      weakWordENorm (paddingDriftBaseAlphabet (d := d) X) Ω I p f = 0 := by
    have hg : hasWeakWordDeriv (paddingDriftBaseAlphabet (d := d) X) Ω I f (fun _ => 0) := by
      apply hasWeakWordDeriv_zero_of_zero_field_mem _ Ω I ((Fin.natAdd q j).succ) hj _ f hf
      simp [paddingDriftBaseAlphabet]
    apply le_antisymm ?_ bot_le
    unfold weakWordENorm
    apply sInf_le
    exact ⟨fun _ => 0, hg, aestronglyMeasurable_const, by simp⟩
  unfold sobolevXENorm
  rw [sum_paddingDrift_wordFamily w _ hzero]
  simp_rw [hword]

end RothschildStein.P1

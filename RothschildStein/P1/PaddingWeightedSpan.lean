-- Copyright (c) 2026 Scott Armstrong and Amélie Loher. All rights reserved.
-- Released under Apache 2.0 license as described in the file LICENSE.
module

public import RothschildStein.P1.PaddingSpanBlocks
public import RothschildStein.P1.PaddingStandardWordEvaluation
public import RothschildStein.P1.PaddingControlDefs
public import RothschildStein.Definitions.StepSpansAt

set_option autoImplicit false
set_option relaxedAutoImplicit false
@[expose] public section
noncomputable section
open Set
namespace RothschildStein.P1

/-- Original generator weights are unchanged by padding. -/
theorem paddingControlWeights_generatorIndex {q d : ℕ}
    (w : Fin (q + 1) → ℕ+) (i : Fin (q + 1)) :
    paddingControlWeights (d := d) w (paddingGeneratorIndex i) = w i := by
  refine Fin.cases ?_ ?_ i
  · rfl
  · intro j
    simp [paddingControlWeights, paddingGeneratorIndex]

/-- Original word weights are unchanged by padding. -/
theorem wordWeight_padding_map {q d : ℕ}
    (w : Fin (q + 1) → ℕ+) (I : List (Fin (q + 1))) :
    wordWeight (paddingControlWeights (d := d) w)
      (I.map paddingGeneratorIndex) = wordWeight w I := by
  simp only [wordWeight, List.map_map, Function.comp_def, paddingControlWeights_generatorIndex]

/-- Weighted bracket spanning survives diffusion padding at
step max s 1: old words retain their exact weight and each added
diffusion is a word of weight one. -/
theorem stepSpansAt_paddingVectorFields {q n d s : ℕ}
    (Ω : Set (Fin n → ℝ)) (hΩ : IsOpen Ω)
    (w : Fin (q + 1) → ℕ+)
    (X : Fin (q + 1) → (Fin n → ℝ) → (Fin n → ℝ))
    (hX : ∀ i, ContDiffOn ℝ (⊤ : ℕ∞) (X i) Ω)
    (ξ : Fin (n + d) → ℝ) (hξ : paddingBaseCLM n d ξ ∈ Ω)
    (hspan : StepSpansAt w s X (paddingBaseCLM n d ξ)) :
    StepSpansAt (paddingControlWeights (d := d) w) (max s 1)
      (paddingVectorFields (d := d) X) ξ := by
  classical
  let M : Submodule ℝ (Fin (n + d) → ℝ) := Submodule.span ℝ
    {v | ∃ I : List (Fin (q + d + 1)), I ≠ [] ∧
      wordWeight (paddingControlWeights (d := d) w) I ≤ max s 1 ∧
      v = wordBracket (paddingVectorFields (d := d) X) I ξ}
  let J : (Fin n → ℝ) →ₗ[ℝ] (Fin (n + d) → ℝ) :=
    ((paddingJoinCLM n d).comp (ContinuousLinearMap.inl ℝ _ _)).toLinearMap
  have hJ (v : Fin n → ℝ) : J v = joinPoint v (0 : Fin d → ℝ) := by
    change paddingJoinCLM n d (v, 0) = _
    exact paddingJoinCLM_apply n d v 0
  have hbase : Submodule.span ℝ
      {v | ∃ I : List (Fin (q + 1)), I ≠ [] ∧ wordWeight w I ≤ s ∧
        v = wordBracket X I (paddingBaseCLM n d ξ)} ≤ M.comap J := by
    apply Submodule.span_le.mpr
    rintro v ⟨I, hI, hweight, rfl⟩
    change J (wordBracket X I (paddingBaseCLM n d ξ)) ∈ M
    rw [hJ]
    have he := wordBracket_padding_map Ω hΩ X hX I hξ
    change wordBracket (paddingVectorFields (d := d) X) (I.map paddingGeneratorIndex) ξ =
      joinPoint (wordBracket X I (paddingBaseCLM n d ξ)) 0 at he
    rw [← he]
    apply Submodule.subset_span
    exact ⟨I.map paddingGeneratorIndex, by simpa using hI,
      by rw [wordWeight_padding_map]; exact hweight.trans (le_max_left s 1), rfl⟩
  have htop : (⊤ : Submodule ℝ (Fin n → ℝ)) ≤ M.comap J := by
    change Submodule.span ℝ _ = ⊤ at hspan
    rw [hspan] at hbase
    exact hbase
  change M = ⊤
  apply submodule_eq_top_of_padding_directions
  · intro v
    rw [← hJ]
    exact htop (Submodule.mem_top : v ∈ (⊤ : Submodule ℝ (Fin n → ℝ)))
  · intro j
    apply Submodule.subset_span
    refine ⟨[(Fin.natAdd q j).succ], by simp, ?_, ?_⟩
    · simp [wordWeight, paddingControlWeights]
    · simp [wordBracket, paddingVectorFields_added, paddingDiffusionField]

end RothschildStein.P1

-- Copyright (c) 2026 Scott Armstrong and Amélie Loher. All rights reserved.
-- Released under Apache 2.0 license as described in the file LICENSE.
module

public import RothschildStein.P1.PaddingSpanBlocks
public import RothschildStein.P1.PaddingNoDriftWordEvaluation
public import RothschildStein.P1.PaddingNoDriftDefs
public import RothschildStein.Definitions.StepSpansAt

set_option autoImplicit false
set_option relaxedAutoImplicit false
@[expose] public section
noncomputable section
open Set
namespace RothschildStein.P1

/-- Original no-drift word weights are preserved under padding. -/
theorem wordWeight_paddingNoDrift_map {q d : ℕ}
    (w : Fin q → ℕ+) (I : List (Fin q)) :
    wordWeight (paddingNoDriftWeights (d := d) w) (I.map (Fin.castAdd d)) = wordWeight w I := by
  simp only [wordWeight, List.map_map, Function.comp_def]
  simp [paddingNoDriftWeights]

/-- Weighted bracket spanning survives diffusion padding at
step max s 1: old words retain their exact weight and each added
diffusion is a word of weight one. -/
theorem stepSpansAt_paddingNoDriftVectorFields {q n d s : ℕ}
    (Ω : Set (Fin n → ℝ)) (hΩ : IsOpen Ω)
    (w : Fin q → ℕ+)
    (X : Fin q → (Fin n → ℝ) → (Fin n → ℝ))
    (hX : ∀ i, ContDiffOn ℝ (⊤ : ℕ∞) (X i) Ω)
    (ξ : Fin (n + d) → ℝ) (hξ : paddingBaseCLM n d ξ ∈ Ω)
    (hspan : StepSpansAt w s X (paddingBaseCLM n d ξ)) :
    StepSpansAt (paddingNoDriftWeights (d := d) w) (max s 1)
      (paddingNoDriftVectorFields (d := d) X) ξ := by
  classical
  let M : Submodule ℝ (Fin (n + d) → ℝ) := Submodule.span ℝ
    {v | ∃ I : List (Fin (q + d)), I ≠ [] ∧
      wordWeight (paddingNoDriftWeights (d := d) w) I ≤ max s 1 ∧
      v = wordBracket (paddingNoDriftVectorFields (d := d) X) I ξ}
  let J : (Fin n → ℝ) →ₗ[ℝ] (Fin (n + d) → ℝ) :=
    ((paddingJoinCLM n d).comp (ContinuousLinearMap.inl ℝ _ _)).toLinearMap
  have hJ (v : Fin n → ℝ) : J v = joinPoint v (0 : Fin d → ℝ) := by
    change paddingJoinCLM n d (v, 0) = _
    exact paddingJoinCLM_apply n d v 0
  have hbase : Submodule.span ℝ
      {v | ∃ I : List (Fin q), I ≠ [] ∧ wordWeight w I ≤ s ∧
        v = wordBracket X I (paddingBaseCLM n d ξ)} ≤ M.comap J := by
    apply Submodule.span_le.mpr
    rintro v ⟨I, hI, hweight, rfl⟩
    change J (wordBracket X I (paddingBaseCLM n d ξ)) ∈ M
    rw [hJ]
    have he := wordBracket_paddingNoDrift_map Ω hΩ X hX I hξ
    change wordBracket (paddingNoDriftVectorFields (d := d) X) (I.map (Fin.castAdd d)) ξ =
      joinPoint (wordBracket X I (paddingBaseCLM n d ξ)) 0 at he
    rw [← he]
    apply Submodule.subset_span
    exact ⟨I.map (Fin.castAdd d), by simpa using hI,
      by rw [wordWeight_paddingNoDrift_map]; exact hweight.trans (le_max_left s 1), rfl⟩
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
    refine ⟨[Fin.natAdd q j], by simp, ?_, ?_⟩
    · simp [wordWeight, paddingNoDriftWeights]
    · simp [wordBracket, paddingNoDriftVectorFields_added, paddingDiffusionField]

end RothschildStein.P1

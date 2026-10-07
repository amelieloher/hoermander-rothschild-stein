-- Copyright (c) 2026 Scott Armstrong and Amélie Loher. All rights reserved.
-- Released under Apache 2.0 license as described in the file LICENSE.
module

public import RothschildStein.P1.PaddingControlSums

set_option autoImplicit false
set_option relaxedAutoImplicit false
@[expose] public section
noncomputable section
open Set MeasureTheory Filter
open scoped BigOperators
namespace RothschildStein.P1

private theorem padding_weight_original {q d : ℕ} (w : Fin (q + 1) → ℕ+)
    (i : Fin (q + 1)) : paddingControlWeights (d := d) w (paddingGeneratorIndex i) = w i := by
  refine Fin.cases ?_ (fun j => ?_) i <;>
    simp [paddingControlWeights, paddingGeneratorIndex]

/-- Every padded controlled curve projects to an original
controlled curve with the same parameter and the original weights.
The controls for added diffusions disappear under projection. -/
theorem isControlledCurve_padding_projection {q n d : ℕ}
    {Ω : Set (Fin n → ℝ)} {U : Set (Fin (n + d) → ℝ)}
    (hU : U ⊆ basePoint ⁻¹' Ω) (w : Fin (q + 1) → ℕ+)
    (X : Fin (q + 1) → (Fin n → ℝ) → (Fin n → ℝ))
    {δ : ℝ} {γ : ℝ → (Fin (n + d) → ℝ)}
    (hγ : isControlledCurve U (paddingControlWeights (d := d) w)
      (paddingVectorFields (d := d) X) δ γ) :
    isControlledCurve Ω w X δ (fun t => basePoint (γ t)) := by
  obtain ⟨hδ, hac, hrange, a, hmeas, ha⟩ := hγ
  refine ⟨hδ, (paddingBaseCLM n d).lipschitzWith.comp_absolutelyContinuousOnInterval hac,
    fun t ht => hU (hrange ht), fun i t => a (paddingGeneratorIndex (d := d) i) t,
    fun i => hmeas _, ?_⟩
  filter_upwards [ha] with t ht
  refine ⟨fun i => ?_, ?_⟩
  · simpa only [padding_weight_original] using ht.1 (paddingGeneratorIndex (d := d) i)
  · have hd := (paddingBaseCLM n d).hasFDerivAt.comp_hasDerivAt t ht.2
    rw [paddingBaseCLM_control_sum] at hd
    exact hd

end RothschildStein.P1

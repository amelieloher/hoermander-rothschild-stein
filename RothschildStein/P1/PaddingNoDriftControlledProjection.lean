-- Copyright (c) 2026 Scott Armstrong and Amélie Loher. All rights reserved.
-- Released under Apache 2.0 license as described in the file LICENSE.
module

public import RothschildStein.P1.PaddingNoDriftControlSums

set_option autoImplicit false
set_option relaxedAutoImplicit false
@[expose] public section
noncomputable section
open Set MeasureTheory Filter
open scoped BigOperators
namespace RothschildStein.P1

private theorem padding_noDrift_weight_original {q d : ℕ} (w : Fin q → ℕ+)
    (i : Fin q) : paddingNoDriftWeights (d := d) w (Fin.castAdd d i) = w i := by
  simp [paddingNoDriftWeights]

/-- Every padded controlled curve projects to an original
controlled curve with the same parameter and the original weights.
The controls for added diffusions disappear under projection. -/
theorem isControlledCurve_paddingNoDrift_projection {q n d : ℕ}
    {Ω : Set (Fin n → ℝ)} {U : Set (Fin (n + d) → ℝ)}
    (hU : U ⊆ basePoint ⁻¹' Ω) (w : Fin q → ℕ+)
    (X : Fin q → (Fin n → ℝ) → (Fin n → ℝ))
    {δ : ℝ} {γ : ℝ → (Fin (n + d) → ℝ)}
    (hγ : isControlledCurve U (paddingNoDriftWeights (d := d) w)
      (paddingNoDriftVectorFields (d := d) X) δ γ) :
    isControlledCurve Ω w X δ (fun t => basePoint (γ t)) := by
  obtain ⟨hδ, hac, hrange, a, hmeas, ha⟩ := hγ
  refine ⟨hδ, (paddingBaseCLM n d).lipschitzWith.comp_absolutelyContinuousOnInterval hac,
    fun t ht => hU (hrange ht), fun i t => a (Fin.castAdd d i) t,
    fun i => hmeas _, ?_⟩
  filter_upwards [ha] with t ht
  refine ⟨fun i => ?_, ?_⟩
  · simpa only [padding_noDrift_weight_original] using ht.1 (Fin.castAdd d i)
  · have hd := (paddingBaseCLM n d).hasFDerivAt.comp_hasDerivAt t ht.2
    rw [paddingBaseCLM_noDrift_control_sum] at hd
    exact hd

end RothschildStein.P1

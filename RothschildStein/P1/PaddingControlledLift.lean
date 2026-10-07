-- Copyright (c) 2026 Scott Armstrong and Amélie Loher. All rights reserved.
-- Released under Apache 2.0 license as described in the file LICENSE.
module

public import RothschildStein.P1.PaddingControlSums
public import Mathlib.Topology.EMetricSpace.Lipschitz
public import Mathlib.Analysis.Calculus.Deriv.Prod

set_option autoImplicit false
set_option relaxedAutoImplicit false
@[expose] public section
noncomputable section
open Set MeasureTheory Filter
open scoped BigOperators
namespace RothschildStein.P1

/-- An original controlled curve lifts with the added variables
constant, using zero added controls and preserving all original weights.
It stays in the specified product cylinder. -/
theorem isControlledCurve_padding_lift {q n d : ℕ}
    {Ω : Set (Fin n → ℝ)} {J : Set (Fin d → ℝ)}
    (w : Fin (q + 1) → ℕ+)
    (X : Fin (q + 1) → (Fin n → ℝ) → (Fin n → ℝ))
    {δ : ℝ} {γ : ℝ → (Fin n → ℝ)}
    (hγ : isControlledCurve Ω w X δ γ) (z : Fin d → ℝ) (hz : z ∈ J) :
    isControlledCurve (basePoint ⁻¹' Ω ∩ paddingFiberCLM n d ⁻¹' J)
      (paddingControlWeights (d := d) w) (paddingVectorFields (d := d) X) δ
      (fun t => joinPoint (γ t) z) := by
  obtain ⟨hδ, hac, hrange, a, hmeas, ha⟩ := hγ
  have hacp := ((paddingJoinCLM n d).lipschitzWith.comp (LipschitzWith.prodMk_right z)).comp_absolutelyContinuousOnInterval hac
  refine ⟨hδ, ?_, ?_, paddingControlCoefficients (d := d) a, ?_, ?_⟩
  · simpa only [Function.comp_def, paddingJoinCLM_apply] using hacp
  · intro t ht
    refine ⟨?_, ?_⟩
    · change basePoint (joinPoint (γ t) z) ∈ Ω
      rw [← paddingBaseCLM_apply, paddingBaseCLM_join]
      exact hrange ht
    · change paddingFiberCLM n d (joinPoint (γ t) z) ∈ J
      rw [paddingFiberCLM_join]
      exact hz
  · intro i
    refine Fin.cases ?_ (fun j => Fin.addCases ?_ ?_ j) i
    · exact hmeas 0
    · intro j
      simpa only [paddingControlCoefficients, Fin.cases_succ, Fin.addCases_left] using hmeas j.succ
    · intro j
      simp only [paddingControlCoefficients, Fin.cases_succ, Fin.addCases_right]
      exact measurable_zero.aemeasurable
  · filter_upwards [ha] with t ht
    refine ⟨?_, ?_⟩
    · intro i
      refine Fin.cases ?_ (fun j => Fin.addCases ?_ ?_ j) i
      · exact ht.1 0
      · intro j
        simpa only [paddingControlCoefficients, paddingControlWeights, Fin.cases_succ, Fin.addCases_left] using ht.1 j.succ
      · intro j
        simp [paddingControlCoefficients, paddingControlWeights, hδ.le]
    · have hd := (paddingJoinCLM n d).hasFDerivAt.comp_hasDerivAt t
        (ht.2.prodMk (hasDerivAt_const t z))
      rw [← paddingJoinCLM_control_sum X a t (γ t) z] at hd
      simpa only [Function.comp_def, paddingJoinCLM_apply] using hd

end RothschildStein.P1

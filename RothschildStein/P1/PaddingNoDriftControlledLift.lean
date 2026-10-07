-- Copyright (c) 2026 Scott Armstrong and Amélie Loher. All rights reserved.
-- Released under Apache 2.0 license as described in the file LICENSE.
module

public import RothschildStein.P1.PaddingNoDriftControlSums
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
theorem isControlledCurve_paddingNoDrift_lift {q n d : ℕ}
    {Ω : Set (Fin n → ℝ)} {J : Set (Fin d → ℝ)}
    (w : Fin q → ℕ+)
    (X : Fin q → (Fin n → ℝ) → (Fin n → ℝ))
    {δ : ℝ} {γ : ℝ → (Fin n → ℝ)}
    (hγ : isControlledCurve Ω w X δ γ) (z : Fin d → ℝ) (hz : z ∈ J) :
    isControlledCurve (basePoint ⁻¹' Ω ∩ paddingFiberCLM n d ⁻¹' J)
      (paddingNoDriftWeights (d := d) w) (paddingNoDriftVectorFields (d := d) X) δ
      (fun t => joinPoint (γ t) z) := by
  obtain ⟨hδ, hac, hrange, a, hmeas, ha⟩ := hγ
  have hacp := ((paddingJoinCLM n d).lipschitzWith.comp (LipschitzWith.prodMk_right z)).comp_absolutelyContinuousOnInterval hac
  refine ⟨hδ, ?_, ?_, paddingNoDriftControlCoefficients (d := d) a, ?_, ?_⟩
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
    refine Fin.addCases ?_ ?_ i
    · intro j
      simpa only [paddingNoDriftControlCoefficients, Fin.addCases_left] using hmeas j
    · intro j
      simp only [paddingNoDriftControlCoefficients, Fin.addCases_right]
      exact measurable_zero.aemeasurable
  · filter_upwards [ha] with t ht
    refine ⟨?_, ?_⟩
    · intro i
      refine Fin.addCases ?_ ?_ i
      · intro j
        simpa only [paddingNoDriftControlCoefficients, paddingNoDriftWeights, Fin.addCases_left] using ht.1 j
      · intro j
        simp [paddingNoDriftControlCoefficients, paddingNoDriftWeights, hδ.le]
    · have hd := (paddingJoinCLM n d).hasFDerivAt.comp_hasDerivAt t
        (ht.2.prodMk (hasDerivAt_const t z))
      rw [← paddingJoinCLM_noDrift_control_sum X a t (γ t) z] at hd
      simpa only [Function.comp_def, paddingJoinCLM_apply] using hd

end RothschildStein.P1

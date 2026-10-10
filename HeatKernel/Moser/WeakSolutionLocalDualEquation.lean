-- Copyright (c) 2026 Scott Armstrong and Amélie Loher. All rights reserved.
-- Released under Apache 2.0 license as described in the file LICENSE.
module

public import HeatKernel.Moser.WeakSolutionRegularizedDualEquation

import all Mathlib.Basic.Real.Basic
import all Mathlib.Analysis.Normed.Group.Continuity
import all Mathlib.Analysis.Normed.Operator.Basic
import all Mathlib.Analysis.Normed.Operator.NormedSpace
import all Mathlib.Topology.Algebra.Module.Spaces.ContinuousLinearMap
import all Mathlib.Topology.Algebra.Module.ContinuousLinearMap.Basic

/-! # Local square-integrable dual time equations -/

@[expose] public section
set_option autoImplicit false
set_option relaxedAutoImplicit false
noncomputable section
open MeasureTheory Set
open scoped ENNReal
namespace HeatKernel

/-- Local square-integrability suffices for the regularized dual equation.
Zero extension is used only outside the compact time domain. -/
theorem SatisfiesDualTimeBalance.ae_forward_difference_eq_of_memLp_restrict
    {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [CompleteSpace E]
    {D F : ℝ → (E →L[ℝ] ℝ)} {a b h : ℝ}
    (hbalance : SatisfiesDualTimeBalance (Icc a b) D F)
    (hD : MemLp D 2 (volume.restrict (Icc a b)))
    (hF : MemLp F 2 (volume.restrict (Icc a b))) (hh : 0 ≤ h) :
    ∀ᵐ t ∂volume, t ∈ Ioo a (b - h) →
      h⁻¹ • (D (t + h) - D t) = -forwardTimeAverage h F t := by
  classical
  let D₀ := (Icc a b).indicator D
  let F₀ := (Icc a b).indicator F
  have hD₀ : MemLp D₀ 2 volume :=
    (memLp_indicator_iff_restrict (f := D) (p := 2) measurableSet_Icc).mpr hD
  have hF₀ : MemLp F₀ 2 volume :=
    (memLp_indicator_iff_restrict (f := F) (p := 2) measurableSet_Icc).mpr hF
  let : IsFiniteMeasure (volume.restrict (Icc a b)) :=
    isFiniteMeasure_restrict.mpr isCompact_Icc.measure_lt_top.ne
  have hiF : Integrable F (volume.restrict (Icc a b)) :=
    hF.integrable (by norm_num)
  have hiF₀ : Integrable F₀ := by
    change Integrable ((Icc a b).indicator F) volume
    rw [integrable_indicator_iff (f := F) (s := Icc a b) (μ := volume) measurableSet_Icc]
    exact hiF
  have heD : D =ᵐ[volume.restrict (Icc a b)] D₀ := by
    filter_upwards [ae_restrict_mem measurableSet_Icc] with t ht
    exact (indicator_of_mem ht D).symm
  have heF : F =ᵐ[volume.restrict (Icc a b)] F₀ := by
    filter_upwards [ae_restrict_mem measurableSet_Icc] with t ht
    exact (indicator_of_mem ht F).symm
  have he := (hbalance.congr heD heF).ae_forward_difference_eq
    (E := E) hD₀ hF₀ hiF₀ hh
  filter_upwards [he] with t ht
  intro hm
  have htJ : t ∈ Icc a b := ⟨hm.1.le, by linarith [hm.2]⟩
  have hthJ : t + h ∈ Icc a b := ⟨by linarith [hm.1], by linarith [hm.2]⟩
  have havg : forwardTimeAverage h F₀ t = forwardTimeAverage h F t := by
    unfold forwardTimeAverage
    congr 1
    apply intervalIntegral.integral_congr
    intro s hs
    have hs' : t ≤ s ∧ s ≤ t + h := by
      simpa only [uIcc_of_le (le_add_of_nonneg_right hh), mem_Icc] using hs
    have hsJ : s ∈ Icc a b := ⟨htJ.1.trans hs'.1, hs'.2.trans hthJ.2⟩
    exact indicator_of_mem hsJ F
  simpa only [D₀, indicator_of_mem htJ, indicator_of_mem hthJ, havg] using ht hm

end HeatKernel

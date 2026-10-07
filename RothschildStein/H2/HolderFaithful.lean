-- Copyright (c) 2026 Scott Armstrong and Amélie Loher. All rights reserved.
-- Released under Apache 2.0 license as described in the file LICENSE.
module

public import RothschildStein.H2.HolderLinear
public import RothschildStein.H2.BallMeasures
public import Mathlib.MeasureTheory.Measure.OpenPos

@[expose] public section
set_option autoImplicit false
set_option relaxedAutoImplicit false
noncomputable section
open Set MeasureTheory Metric Filter
open scoped NNReal ENNReal Topology

namespace RothschildStein.H2
variable {X : Type*} [MetricSpace X] [MeasurableSpace X] [BorelSpace X]

omit [MeasurableSpace X] [BorelSpace X] in
/-- Hölder functions are continuous on their patch. -/
theorem BoundedHolder.continuousOn {δ : ℝ≥0} {U : Set X} {f : X → ℝ}
    (hf : BoundedHolder δ U f) (hδ : 0 < δ) : ContinuousOn f U := by
  exact continuousOn_iff_continuous_domRestrict.mpr
    ((eHolderNorm_lt_top.mp hf.parts.2).holderWith.continuous hδ)

/-- On an open subset of Ω₁, equal L² classes of continuous
functions have equal pointwise representatives. Positive local balls provide
faithfulness; no global full-support hypothesis is imposed. -/
theorem LocDoubling.eqOn_of_ae_eq (D : LocDoubling X) {U : Set X}
    (hU : IsOpen U) (hU₁ : U ⊆ D.Ω₁) {f g : X → ℝ}
    (hf : ContinuousOn f U) (hg : ContinuousOn g U)
    (hfg : f =ᵐ[D.μ.restrict U] g) : EqOn f g U := by
  have hn : D.μ (U ∩ {x | f x ≠ g x}) = 0 := by
    have h := ae_imp_of_ae_restrict hfg
    change D.μ {x | x ∈ U ∧ ¬f x = g x} = 0
    simpa only [ae_iff, Classical.not_imp] using h
  have ho : IsOpen (U ∩ {x | f x ≠ g x}) := by
    refine isOpen_iff_mem_nhds.mpr fun x hx => inter_mem (hU.mem_nhds hx.1) ?_
    exact (hf.continuousAt (hU.mem_nhds hx.1)).prodMk_nhds
      (hg.continuousAt (hU.mem_nhds hx.1))
      (isClosed_diagonal.isOpen_compl.mem_nhds hx.2)
  intro x hx
  by_contra hne
  obtain ⟨r, hr, hb⟩ := Metric.isOpen_iff.mp ho x ⟨hx, hne⟩
  let s := min r D.κ
  have hs : 0 < s := lt_min hr D.κ_pos
  have hsκ : s ≤ 6 * D.κ := (min_le_right _ _).trans (by linarith [D.κ_pos])
  have hpos := (D.outerPatch.doubling x (hU₁ hx) s hs hsκ).1
  change 0 < D.μ (ball x s) at hpos
  have hzero := measure_mono_null ((ball_subset_ball (min_le_left r D.κ)).trans hb) hn
  exact hpos.ne' hzero

end RothschildStein.H2

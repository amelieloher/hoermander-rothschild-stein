-- Copyright (c) 2026 Scott Armstrong and Amélie Loher. All rights reserved.
-- Released under Apache 2.0 license as described in the file LICENSE.
module

public import Mathlib.MeasureTheory.Function.L2Space
public import Mathlib.MeasureTheory.Integral.Prod
public import Mathlib.Topology.Compactness.Lindelof
public import Mathlib.Analysis.Normed.Module.Basic
import Mathlib.MeasureTheory.Function.SpecialFunctions.Basic
import Mathlib.Tactic.NormNum

/-!
# Measurable curves in spatial L² and closed subspaces

Distances to fixed L² classes are measurable integrals of jointly measurable representatives.
In a separable L² space this gives strong measurability of the curve. An embedding then transfers
strong measurability to a closed graph carrier.
-/

@[expose] public section

noncomputable section

open Set MeasureTheory
open scoped ENNReal Topology

namespace HeatKernel

/-- A map into a second countable metric space is measurable when all its distances to fixed
points are measurable. -/
theorem measurable_of_measurable_dist {α V : Type*} [MeasurableSpace α] [MetricSpace V]
    [SecondCountableTopology V] [MeasurableSpace V] [BorelSpace V] {f : α → V}
    (hf : ∀ v, Measurable (fun a => dist (f a) v)) : Measurable f := by
  apply measurable_of_isOpen
  intro s hs
  choose r hr hrs using fun x : s => Metric.isOpen_iff.mp hs x x.property
  have hc : s ⊆ ⋃ x : s, Metric.ball (x : V) (r x) := by
    intro x hx
    exact mem_iUnion.mpr ⟨⟨x, hx⟩, Metric.mem_ball_self (hr ⟨x, hx⟩)⟩
  obtain ⟨t, ht, hcover⟩ := (HereditarilyLindelofSpace.isLindelof s).elim_countable_subcover
    (fun x : s => Metric.ball (x : V) (r x)) (fun _ => Metric.isOpen_ball) hc
  have heq : s = ⋃ x ∈ t, Metric.ball (x : V) (r x) := by
    apply Subset.antisymm hcover
    exact iUnion₂_subset fun x _ => hrs x
  rw [heq, preimage_iUnion₂]
  exact MeasurableSet.biUnion ht fun x _ => measurableSet_lt (hf x) measurable_const

/-- Almost everywhere measurable distances suffice for almost everywhere measurability. -/
theorem aemeasurable_of_aemeasurable_dist {α V : Type*} [MeasurableSpace α] [MetricSpace V]
    [SecondCountableTopology V] [MeasurableSpace V] [BorelSpace V] {μ : Measure α}
    {f : α → V} (hf : ∀ v, AEMeasurable (fun a => dist (f a) v) μ) :
    AEMeasurable f μ := by
  have hn : NullMeasurable f μ := by
    change @Measurable (NullMeasurableSpace α μ) V _ _ f
    exact measurable_of_measurable_dist fun v => (hf v).nullMeasurable.measurable'
  exact hn.aemeasurable

/-- A jointly almost everywhere strongly measurable representative gives an almost everywhere
strongly measurable L²-valued curve, with no choice of spatial representatives as a premise. -/
theorem aestronglyMeasurable_L2_of_representatives {α β E : Type*}
    [MeasurableSpace α] [MeasurableSpace β] [NormedAddCommGroup E]
    [MeasurableSpace E] [BorelSpace E] [SecondCountableTopology E]
    {μ : Measure α} {ν : Measure β} [SFinite ν]
    [SecondCountableTopology (Lp E 2 ν)] {U : α → Lp E 2 ν} {u : α → β → E}
    (hu : AEStronglyMeasurable (Function.uncurry u) (μ.prod ν))
    (hrep : ∀ᵐ a ∂μ, U a =ᵐ[ν] u a) : AEStronglyMeasurable U μ := by
  borelize ↥(Lp E 2 ν)
  apply AEMeasurable.aestronglyMeasurable
  apply aemeasurable_of_aemeasurable_dist
  intro v
  have hj : AEMeasurable (fun z : α × β => ‖u z.1 z.2 - v z.2‖ₑ ^ (2 : ℝ))
      (μ.prod ν) := by
    exact ((hu.sub ((Lp.stronglyMeasurable v).comp_measurable measurable_snd).aestronglyMeasurable).enorm).pow_const _
  have hi := (hj.lintegral_prod_right' (ν := ν)).pow_const (1 / (2 : ℝ))
  have hm := hi.ennreal_toReal
  apply hm.congr
  filter_upwards [hrep] with a ha
  rw [dist_edist, Lp.edist_def]
  have hs : AEStronglyMeasurable (u a - ⇑v) ν :=
    ((Lp.aestronglyMeasurable (U a)).congr ha).sub (Lp.aestronglyMeasurable v)
  rw [eLpNorm_congr_ae (ha.sub Filter.EventuallyEq.rfl),
    eLpNorm_eq_lintegral_rpow_enorm_toReal (by norm_num : (2 : ℝ≥0∞) ≠ 0)
      (by norm_num : (2 : ℝ≥0∞) ≠ ⊤) hs]
  simp only [ENNReal.toReal_ofNat, Pi.sub_apply]

/-- Almost everywhere strong measurability also transfers to a subspace-valued curve. -/
theorem aestronglyMeasurable_submodule_of_coe {α V : Type*} [MeasurableSpace α]
    [NormedAddCommGroup V] [NormedSpace ℝ V] {μ : Measure α}
    {S : Submodule ℝ V} {u : α → S}
    (hu : AEStronglyMeasurable (fun a => (u a : V)) μ) : AEStronglyMeasurable u μ := by
  exact Topology.IsEmbedding.subtypeVal.aestronglyMeasurable_comp_iff.mp hu

/-- Membership in a Bochner Lp space can be checked after including a subspace in its ambient
normed space. The subspace carries the induced norm. -/
theorem memLp_submodule_iff_coe {α V : Type*} [MeasurableSpace α]
    [NormedAddCommGroup V] [NormedSpace ℝ V] {μ : Measure α}
    {S : Submodule ℝ V} {u : α → S} {p : ℝ≥0∞} :
    MemLp u p μ ↔ MemLp (fun a => (u a : V)) p μ := by
  constructor
  · intro h
    have hm := continuous_subtype_val.comp_aestronglyMeasurable h.aestronglyMeasurable
    rw [memLp_iff, eLpNorm_congr_norm_ae hm h.aestronglyMeasurable
      (Filter.Eventually.of_forall fun _ => rfl)]
    exact h.eLpNorm_lt_top
  · intro h
    have hm := aestronglyMeasurable_submodule_of_coe h.aestronglyMeasurable
    rw [memLp_iff, eLpNorm_congr_norm_ae hm h.aestronglyMeasurable
      (Filter.Eventually.of_forall fun _ => rfl)]
    exact h.eLpNorm_lt_top

/-- A continuous linear equivalence preserves the Bochner Lp class. -/
theorem memLp_comp_continuousLinearEquiv_iff {α V W : Type*} [MeasurableSpace α]
    [NormedAddCommGroup V] [NormedSpace ℝ V] [NormedAddCommGroup W] [NormedSpace ℝ W]
    {μ : Measure α} {p : ℝ≥0∞} (e : V ≃L[ℝ] W) (f : α → V) :
    MemLp (e ∘ f) p μ ↔ MemLp f p μ := by
  constructor
  · intro h
    have heq : e.symm ∘ (e ∘ f) = f := by
      funext a
      exact e.symm_apply_apply (f a)
    rw [← heq]
    exact e.symm.toContinuousLinearMap.comp_memLp' h
  · exact e.toContinuousLinearMap.comp_memLp'

end HeatKernel

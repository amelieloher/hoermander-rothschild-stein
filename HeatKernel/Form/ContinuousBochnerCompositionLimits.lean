-- Copyright (c) 2026 Scott Armstrong and Amélie Loher. All rights reserved.
-- Released under Apache 2.0 license as described in the file LICENSE.
module

public import Mathlib.MeasureTheory.Function.UniformIntegrable
public import Mathlib.MeasureTheory.Function.ConvergenceInMeasure
public import Mathlib.Topology.Sequences
import Mathlib.Tactic.Linter

/-! # Bochner L² limits under continuous maps with linear growth -/

@[expose] public section

noncomputable section

open MeasureTheory Filter TopologicalSpace
open scoped NNReal ENNReal Topology

namespace HeatKernel

variable {T E F : Type*} [MeasurableSpace T] {μ : Measure T}
    [NormedAddCommGroup E] [NormedSpace ℝ E]
    [NormedAddCommGroup F]
    {P : E → F} (hP : Continuous P) {C : ℝ≥0} (hb : ∀ u, ‖P u‖ ≤ (C : ℝ) * ‖u‖)

include hP hb

/-- A continuous map with a linear norm bound preserves Bochner Lᵖ functions. -/
theorem memLp_comp_of_continuous_norm_le {p : ℝ≥0∞} {v : T → E} (hv : MemLp v p μ) :
    MemLp (fun t => P (v t)) p μ := by
  apply (hv.const_smul (C : ℝ)).of_le (hP.comp_aestronglyMeasurable hv.aestronglyMeasurable)
  exact Eventually.of_forall fun t => by
    simpa only [Pi.smul_apply, norm_smul, Real.norm_of_nonneg C.coe_nonneg] using hb (v t)

/-- On a finite measure space, continuous maps with linear growth carry L² convergence to
L² convergence. Uniform integrability supplies the domination needed for the nonlinear map. -/
theorem tendsto_eLpNorm_comp_of_tendsto_Lp [IsFiniteMeasure μ]
    {v : ℕ → Lp E 2 μ} {u : Lp E 2 μ} (hv : Tendsto v atTop (𝓝 u)) :
    Tendsto (fun n => eLpNorm (fun t => P (v n t) - P (u t)) 2 μ) atTop (𝓝 0) := by
  have hmem : ∀ n, MemLp (fun t => P (v n t)) 2 μ := fun n =>
    memLp_comp_of_continuous_norm_le hP hb (Lp.memLp (v n))
  have humem : MemLp (fun t => P (u t)) 2 μ :=
    memLp_comp_of_continuous_norm_le hP hb (Lp.memLp u)
  apply Filter.tendsto_of_subseq_tendsto
  intro ns hns
  obtain ⟨ms, hms, hae⟩ := (tendstoInMeasure_of_tendsto_Lp (hv.comp hns)).exists_seq_tendsto_ae
  have hs : Tendsto (fun n => (C : ℝ) • v (ns (ms n))) atTop (𝓝 ((C : ℝ) • u)) :=
    (hv.comp (hns.comp hms.tendsto_atTop)).const_smul (C : ℝ)
  have hui := unifIntegrable_of_tendsto_Lp (p := (2 : ℝ≥0∞)) (by norm_num) (by norm_num)
    (fun n => Lp.memLp ((C : ℝ) • v (ns (ms n)))) (Lp.memLp ((C : ℝ) • u))
    ((Lp.tendsto_Lp_iff_tendsto_eLpNorm' _ _).mp hs)
  have hdom : ∀ n, ∀ᵐ t ∂μ, ‖P (v (ns (ms n)) t)‖ ≤ ‖((C : ℝ) • v (ns (ms n))) t‖ := by
    intro n
    filter_upwards [Lp.coeFn_smul (C : ℝ) (v (ns (ms n)))] with t ht
    rw [ht]
    simpa only [Pi.smul_apply, norm_smul, Real.norm_of_nonneg C.coe_nonneg] using hb (v (ns (ms n)) t)
  have hpi : UnifIntegrable (fun n t => P (v (ns (ms n)) t)) 2 μ := by
    apply unifIntegrable_iff.mpr
    intro ε hε
    obtain ⟨δ, hδ, hd⟩ := unifIntegrable_iff.mp hui ε hε
    refine ⟨δ, hδ, fun n s hs => ?_⟩
    exact (eLpNorm_mono_ae (hmem (ns (ms n))).aestronglyMeasurable.restrict
      ((hdom n).filter_mono ae_restrict_le)).trans (hd n s hs)
  refine ⟨ms, ?_⟩
  exact tendsto_Lp_finite_of_tendsto_ae (by norm_num) (by norm_num)
    (fun n => (hmem (ns (ms n))).aestronglyMeasurable) humem hpi
    (hae.mono fun t ht => hP.continuousAt.tendsto.comp ht)



end HeatKernel

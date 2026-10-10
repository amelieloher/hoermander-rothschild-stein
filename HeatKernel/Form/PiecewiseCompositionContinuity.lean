-- Copyright (c) 2026 Scott Armstrong and Amélie Loher. All rights reserved.
-- Released under Apache 2.0 license as described in the file LICENSE.
module

public import HeatKernel.Form.CountableExceptionalChainRule
public import HeatKernel.Form.BoundedCoefficientLimits
public import Mathlib.Analysis.Calculus.FDeriv.Measurable
public import Mathlib.Analysis.Calculus.ContDiff.Deriv
public import Mathlib.Topology.Sequences
import Mathlib.Tactic.Linter

/-! # Continuity of scalar composition outside countable exceptional levels -/

@[expose] public section

noncomputable section

open Set MeasureTheory Filter TopologicalSpace
open scoped ENNReal NNReal Topology

namespace HeatKernel

/-- A Lipschitz scalar map that is locally C¹ outside countably many levels acts continuously
on the horizontal energy graph whenever its representatives satisfy the exact chain identities. -/
theorem continuous_energyGraph_composition_off_countable {N q : ℕ}
    (X : Fin q → (Fin N → ℝ) → (Fin N → ℝ))
    (hX : ∀ i, ContDiff ℝ (⊤ : ℕ∞) (X i))
    {η : ℝ → ℝ} {C : ℝ≥0} (hLip : LipschitzWith C η) (hzero : η 0 = 0)
    (S : Set ℝ) (hS : S.Countable) (hη : ∀ s ∉ S, ContDiffAt ℝ 1 η s)
    (c : energyGraph (N := N) ⊤ X → energyGraph (N := N) ⊤ X)
    (hcf : ∀ w, (c w : GradientSpace (N := N) ⊤ q).fst =ᵐ[volume]
      fun x => η ((w : GradientSpace (N := N) ⊤ q).fst x))
    (hcg : ∀ w i, (c w : GradientSpace (N := N) ⊤ q).snd i =ᵐ[volume]
      fun x => deriv η ((w : GradientSpace (N := N) ⊤ q).fst x) *
        (w : GradientSpace (N := N) ⊤ q).snd i x) : Continuous c := by
  have hb : ∀ s, ‖deriv η s‖ ≤ C := fun _ => norm_deriv_le_of_lipschitz hLip
  have hm : Measurable (deriv η) := measurable_deriv η
  have hfun : ∀ w, (c w : GradientSpace (N := N) ⊤ q).fst =
      hLip.compLp hzero (w : GradientSpace (N := N) ⊤ q).fst := by
    intro w
    apply Lp.ext
    have H := hLip.coeFn_compLp hzero (w : GradientSpace (N := N) ⊤ q).fst
    simp only [Opens.coe_top, Measure.restrict_univ] at H ⊢
    exact (hcf w).trans H.symm
  apply continuous_iff_seqContinuous.mpr
  intro v u hu
  apply Filter.tendsto_of_subseq_tendsto
  intro ns hns
  have hcoord := (tendsto_GradientSpace_iff (N := N) (q := q) ⊤).mp
    (tendsto_subtype_rng.mp (hu.comp hns))
  obtain ⟨ms, hms, hae⟩ := (tendstoInMeasure_of_tendsto_Lp hcoord.1).exists_seq_tendsto_ae
  refine ⟨ms, tendsto_subtype_rng.mpr ((tendsto_GradientSpace_iff ⊤).mpr ⟨?_, ?_⟩)⟩
  · simpa only [Function.comp_def, hfun] using (hLip.continuous_compLp hzero).continuousAt.tendsto.comp
      (hcoord.1.comp hms.tendsto_atTop)
  · intro i
    have hz : ∀ᵐ x ∂volume.restrict (⊤ : Opens (Fin N → ℝ)),
        (u : GradientSpace (N := N) ⊤ q).fst x ∈ S →
          (u : GradientSpace (N := N) ⊤ q).snd i x = 0 := by
      simpa only [Opens.coe_top, Measure.restrict_univ] using
        energyGraph_gradient_zero_on_countable_levels X hX u S hS i
    have hp : ∀ᵐ x ∂volume.restrict (⊤ : Opens (Fin N → ℝ)),
        Tendsto (fun n => deriv η ((v (ns (ms n)) : GradientSpace (N := N) ⊤ q).fst x) *
          (u : GradientSpace (N := N) ⊤ q).snd i x) atTop
          (𝓝 (deriv η ((u : GradientSpace (N := N) ⊤ q).fst x) *
            (u : GradientSpace (N := N) ⊤ q).snd i x)) := by
      filter_upwards [hae, hz] with x hx hzx
      by_cases hs : (u : GradientSpace (N := N) ⊤ q).fst x ∈ S
      · simp only [hzx hs, mul_zero]
        exact tendsto_const_nhds
      · have hd : ContinuousAt (deriv η) ((u : GradientSpace (N := N) ⊤ q).fst x) :=
          ((hη _ hs).derivWithin (m := 0) (by simp)).continuousAt
        exact (hd.tendsto.comp hx).mul_const _
    apply tendsto_L2_mul_of_bounded
      (fun n => (hm.comp_aemeasurable
        (Lp.memLp (v (ns (ms n)) : GradientSpace (N := N) ⊤ q).fst).aemeasurable).aestronglyMeasurable)
      ((hm.comp_aemeasurable (Lp.memLp (u : GradientSpace (N := N) ⊤ q).fst).aemeasurable).aestronglyMeasurable)
      C.coe_nonneg
      (fun n => Eventually.of_forall fun x => hb ((v (ns (ms n)) : GradientSpace (N := N) ⊤ q).fst x))
      (Eventually.of_forall fun x => hb ((u : GradientSpace (N := N) ⊤ q).fst x))
      hp ((hcoord.2 i).comp hms.tendsto_atTop)
    · intro n
      simpa only [Opens.coe_top, Measure.restrict_univ, Function.comp_def] using hcg (v (ns (ms n))) i
    · simpa only [Opens.coe_top, Measure.restrict_univ, Function.comp_def] using hcg u i



end HeatKernel

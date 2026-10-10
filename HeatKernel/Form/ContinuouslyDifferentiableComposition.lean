-- Copyright (c) 2026 Scott Armstrong and Amélie Loher. All rights reserved.
-- Released under Apache 2.0 license as described in the file LICENSE.
module

public import HeatKernel.Form.ScalarComposition
public import HeatKernel.Form.GraphForm
import Mathlib.Tactic.Linarith
public import HeatKernel.Form.CompactGradientApproximation
public import Mathlib.Analysis.Calculus.MeanValue

/-!
# Continuously differentiable scalar composition

A continuously differentiable scalar function vanishing at zero with bounded derivative
preserves the global energy domain. Compact compositions of core representatives are first
identified by their weak gradients, then approximated in the graph norm.
-/

@[expose] public section

noncomputable section

open Set MeasureTheory Filter TopologicalSpace RothschildStein
open scoped ENNReal NNReal Topology

namespace HeatKernel

/-- The C¹ scalar chain rule in the global closed horizontal energy domain. -/
theorem exists_energyGraph_comp_contDiff_one {N q : ℕ}
    (X : Fin q → (Fin N → ℝ) → (Fin N → ℝ))
    (hX : ∀ i, ContDiff ℝ (⊤ : ℕ∞) (X i))
    (v : energyGraph (N := N) ⊤ X) {η : ℝ → ℝ}
    (hη : ContDiff ℝ 1 η) (hzero : η 0 = 0) {C : ℝ≥0}
    (hbound : ∀ s, ‖deriv η s‖ ≤ C) :
    ∃ z : energyGraph (N := N) ⊤ X,
      (z : GradientSpace (N := N) ⊤ q).fst =ᵐ[volume]
        (fun x => η ((v : GradientSpace (N := N) ⊤ q).fst x)) ∧
      ∀ i, (z : GradientSpace (N := N) ⊤ q).snd i =ᵐ[volume]
        (fun x => deriv η ((v : GradientSpace (N := N) ⊤ q).fst x) * (v : GradientSpace (N := N) ⊤ q).snd i x) := by
  let U : Opens (Fin N → ℝ) := ⊤
  let μ := volume.restrict (U : Set (Fin N → ℝ))
  have hLip : LipschitzWith C η := lipschitzWith_of_nnnorm_deriv_le
    (hη.differentiable (by simp)) (fun s => by exact_mod_cast hbound s)
  have hm : ∀ (w : GradientSpace U q) i,
      MemLp (fun x => deriv η (w.fst x) * w.snd i x) 2 μ := by
    intro w i
    exact memLp_mul_of_ae_bound
      (hη.continuous_deriv_one.comp_aestronglyMeasurable (Lp.memLp w.fst).aestronglyMeasurable)
      (Lp.memLp (w.snd i)) C.coe_nonneg (Eventually.of_forall fun x => hbound (w.fst x))
  let c : GradientSpace U q → GradientSpace U q := fun w =>
    WithLp.toLp 2 (hLip.compLp hzero w.fst,
      WithLp.toLp 2 (fun i => (hm w i).toLp (fun x => deriv η (w.fst x) * w.snd i x)))
  have hcf : ∀ w, (c w).fst =ᵐ[μ] fun x => η (w.fst x) := fun w => hLip.coeFn_compLp hzero w.fst
  have hcg : ∀ w i, (c w).snd i =ᵐ[μ] fun x => deriv η (w.fst x) * w.snd i x := by
    intro w i
    dsimp only [c]
    exact (hm w i).coeFn_toLp
  have hcore : ∀ w ∈ smoothGradientPairs U X, c w ∈ energyGraph U X := by
    intro w hw
    obtain ⟨f, hf, hc, _, hwf, hwg⟩ := hw
    have hcomp : ContDiff ℝ 1 (η ∘ f) := hη.comp (hf.of_le (by simp))
    have hfun : (c w).fst =ᵐ[μ] η ∘ f := (hcf w).trans (hwf.fun_comp η)
    have hgrad : ∀ i, (c w).snd i =ᵐ[μ] fieldDerivative (X i) (η ∘ f) := by
      intro i
      apply (hcg w i).trans
      filter_upwards [hwf, hwg i] with x hfx hix
      rw [fieldDerivative_comp (X i) (hη.differentiable (by simp))
        (hf.differentiable (by simp)), hfx, hix]
    have hweak : ∀ i, hasWeakWordDeriv X U [i] (c w).fst ((c w).snd i) := by
      intro i
      have H := S.hasWeakWordDeriv_classical_finite U X (fun j => (hX j).contDiffOn)
        [i] (η ∘ f) (by simpa using hcomp.contDiffOn)
      have H' : hasWeakWordDeriv X U [i] (η ∘ f) (fieldDerivative (X i) (η ∘ f)) := by
        simpa only [wordDerivative, Function.comp_def] using H
      exact S.hasWeakWordDeriv_congr_ae X U H' hfun.symm (hgrad i).symm
    apply mem_energyGraph_of_compact_weakGradient X hX ⟨c w, hweak⟩ (hc.comp_left hzero)
    simpa only [μ, U, Opens.coe_top, Measure.restrict_univ] using hfun
  obtain ⟨w, hw, ht⟩ := exists_smoothGradientPairs_tendsto U X v
  have hcoord := (tendsto_GradientSpace_iff U).mp ht
  obtain ⟨ns, hns, hae⟩ := (tendstoInMeasure_of_tendsto_Lp hcoord.1).exists_seq_tendsto_ae
  have hmem : c v ∈ energyGraph U X := by
    apply mem_energyGraph_of_componentwise_tendsto U X (v := fun n => c (w (ns n)))
    · exact fun n => hcore _ (hw (ns n))
    · exact (hLip.continuous_compLp hzero).continuousAt.tendsto.comp
        (hcoord.1.comp hns.tendsto_atTop)
    · intro i
      exact tendsto_L2_mul_of_bounded
        (fun n => hη.continuous_deriv_one.comp_aestronglyMeasurable
          (Lp.memLp (w (ns n)).fst).aestronglyMeasurable)
        (hη.continuous_deriv_one.comp_aestronglyMeasurable
          (Lp.memLp (v : GradientSpace U q).fst).aestronglyMeasurable) C.coe_nonneg
        (fun n => Eventually.of_forall fun x => hbound ((w (ns n)).fst x))
        (Eventually.of_forall fun x => hbound ((v : GradientSpace U q).fst x))
        (hae.mono fun x hx => (hη.continuous_deriv_one.continuousAt.tendsto.comp hx).mul_const _)
        ((hcoord.2 i).comp hns.tendsto_atTop) (fun n => hcg (w (ns n)) i) (hcg v i)
  refine ⟨⟨c v, hmem⟩, ?_, fun i => ?_⟩
  · simpa only [μ, U, Opens.coe_top, Measure.restrict_univ] using hcf v
  · simpa only [μ, U, Opens.coe_top, Measure.restrict_univ] using hcg v i

/-- The C¹ chain rule with its horizontal energy estimate. -/
theorem exists_energyGraph_comp_contDiff_one_energy_le {N q : ℕ}
    (X : Fin q → (Fin N → ℝ) → (Fin N → ℝ))
    (hX : ∀ i, ContDiff ℝ (⊤ : ℕ∞) (X i))
    (v : energyGraph (N := N) ⊤ X) {η : ℝ → ℝ}
    (hη : ContDiff ℝ 1 η) (hzero : η 0 = 0) {C : ℝ≥0}
    (hbound : ∀ s, ‖deriv η s‖ ≤ C) :
    ∃ z : energyGraph (N := N) ⊤ X,
      (z : GradientSpace (N := N) ⊤ q).fst =ᵐ[volume]
        (fun x => η ((v : GradientSpace (N := N) ⊤ q).fst x)) ∧
      (∀ i, (z : GradientSpace (N := N) ⊤ q).snd i =ᵐ[volume]
        (fun x => deriv η ((v : GradientSpace (N := N) ⊤ q).fst x) *
          (v : GradientSpace (N := N) ⊤ q).snd i x)) ∧
      horizontalEnergy ⊤ X z z ≤ (C : ℝ) ^ 2 * horizontalEnergy ⊤ X v v := by
  obtain ⟨z, hzf, hzg⟩ := exists_energyGraph_comp_contDiff_one X hX v hη hzero hbound
  refine ⟨z, hzf, hzg, ?_⟩
  have hnorm : ∀ i, ‖(z : GradientSpace (N := N) ⊤ q).snd i‖ ≤
      C * ‖(v : GradientSpace (N := N) ⊤ q).snd i‖ := by
    intro i
    apply Lp.norm_le_mul_norm_of_ae_le_mul
    have H : (z : GradientSpace (N := N) ⊤ q).snd i =ᵐ[
        volume.restrict (⊤ : Opens (Fin N → ℝ))] fun x =>
        deriv η ((v : GradientSpace (N := N) ⊤ q).fst x) *
          (v : GradientSpace (N := N) ⊤ q).snd i x := by
      simpa only [Opens.coe_top, Measure.restrict_univ] using hzg i
    filter_upwards [H] with x hx
    rw [hx, norm_mul]
    exact mul_le_mul_of_nonneg_right (hbound _) (norm_nonneg _)
  simp only [horizontalEnergy, energyGradient_apply, real_inner_self_eq_norm_sq,
    PiLp.norm_sq_eq_of_L2]
  rw [Finset.mul_sum]
  apply Finset.sum_le_sum
  intro i _
  have h := hnorm i
  have hn := norm_nonneg ((z : GradientSpace (N := N) ⊤ q).snd i)
  have hm := norm_nonneg ((v : GradientSpace (N := N) ⊤ q).snd i)
  nlinarith [mul_nonneg C.coe_nonneg hm]

end HeatKernel

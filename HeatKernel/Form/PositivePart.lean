-- Copyright (c) 2026 Scott Armstrong and Amélie Loher. All rights reserved.
-- Released under Apache 2.0 license as described in the file LICENSE.
module

public import HeatKernel.Form.PositivePartApproximation
public import Mathlib.Analysis.Calculus.Deriv.Shift
public import HeatKernel.Form.ContinuouslyDifferentiableComposition
public import HeatKernel.Form.LipschitzCompositionLimits
import Mathlib.Tactic.Positivity

/-!
# Positive-part differentiation in the energy domain

The derivative of the positive part is the original horizontal derivative on the strict
positive set and zero on its complement, including the zero level.
-/

@[expose] public section

noncomputable section

open Set MeasureTheory Filter TopologicalSpace
open scoped Topology NNReal

namespace HeatKernel

/-- Positive parts belong to the global energy domain, with the strict positive-set
horizontal derivative formula. -/
theorem exists_energyGraph_positiveLevel {N q : ℕ}
    (X : Fin q → (Fin N → ℝ) → (Fin N → ℝ))
    (hX : ∀ i, ContDiff ℝ (⊤ : ℕ∞) (X i)) (v : energyGraph (N := N) ⊤ X)
    (c : ℝ) (hc : 0 ≤ c) :
    ∃ z : energyGraph (N := N) ⊤ X,
      (z : GradientSpace (N := N) ⊤ q).fst =ᵐ[volume]
        (fun x => max ((v : GradientSpace (N := N) ⊤ q).fst x - c) 0) ∧
      ∀ i, (z : GradientSpace (N := N) ⊤ q).snd i =ᵐ[volume]
        (fun x => if c < (v : GradientSpace (N := N) ⊤ q).fst x
          then (v : GradientSpace (N := N) ⊤ q).snd i x else 0) := by
  let U : Opens (Fin N → ℝ) := ⊤
  let μ := volume.restrict (U : Set (Fin N → ℝ))
  let ε : ℕ → ℝ := fun n => 1 / (n + 1 : ℝ)
  have hεpos : ∀ n, 0 < ε n := fun n => by dsimp [ε]; positivity
  have hε : Tendsto ε atTop (𝓝 0) := tendsto_one_div_add_atTop_nhds_zero_nat
  let a : ℕ → ℝ → ℝ := fun n s => positivePartApproximation (ε n) (s - c)
  have ha : ∀ n, ContDiff ℝ 1 (a n) := fun n =>
    (contDiff_one_positivePartApproximation (ε n)).comp (contDiff_id.sub contDiff_const)
  have ha0 : ∀ n, a n 0 = 0 := fun n =>
    positivePartApproximation_of_nonpos (hεpos n) (by linarith)
  have hab : ∀ n s, ‖deriv (a n) s‖ ≤ 1 := fun n s => by
    simpa only [a, deriv_comp_sub_const] using norm_deriv_positivePartApproximation_le (ε n) (s - c)
  have haLip : ∀ n, LipschitzWith 1 (a n) := fun n =>
    lipschitzWith_of_nnnorm_deriv_le ((ha n).differentiable (by simp))
      (fun s => by exact_mod_cast hab n s)
  let b : ℝ → ℝ := fun s => if c < s then 1 else 0
  have hb : Measurable b := Measurable.ite measurableSet_Ioi measurable_const measurable_const
  have hbnd : ∀ s, ‖b s‖ ≤ 1 := by intro s; dsimp [b]; split <;> norm_num
  have hbm : AEStronglyMeasurable (fun x => b ((v : GradientSpace U q).fst x)) μ :=
    (hb.comp_aemeasurable (Lp.memLp (v : GradientSpace U q).fst).aemeasurable).aestronglyMeasurable
  have hmg : ∀ i, MemLp (fun x => b ((v : GradientSpace U q).fst x) *
      (v : GradientSpace U q).snd i x) 2 μ := fun i =>
    memLp_mul_of_ae_bound hbm (Lp.memLp _) zero_le_one (Eventually.of_forall fun x => hbnd _)
  let η : ℝ → ℝ := fun s => max (s - c) 0
  have hηLip : LipschitzWith 1 η := by
    apply LipschitzWith.of_dist_le_mul
    intro x y
    simpa only [η, dist_sub_right] using Lp.lipschitzWith_pos_part.dist_le_mul (x - c) (y - c)
  have hzero : η 0 = 0 := max_eq_right (by linarith)
  let z : GradientSpace U q := WithLp.toLp 2
    (hηLip.compLp hzero (v : GradientSpace U q).fst,
      WithLp.toLp 2 (fun i => (hmg i).toLp (fun x => b ((v : GradientSpace U q).fst x) *
        (v : GradientSpace U q).snd i x)))
  have hzg : ∀ i, z.snd i =ᵐ[μ] fun x => b ((v : GradientSpace U q).fst x) *
      (v : GradientSpace U q).snd i x := by
    intro i
    dsimp only [z]
    exact (hmg i).coeFn_toLp
  choose w hwf hwg using fun n => exists_energyGraph_comp_contDiff_one X hX v (ha n) (ha0 n)
    (C := 1) (by simpa using hab n)
  have hwf' : ∀ n, (w n : GradientSpace U q).fst =ᵐ[μ]
      fun x => a n ((v : GradientSpace U q).fst x) := by
    simpa only [μ, U, Opens.coe_top, Measure.restrict_univ] using hwf
  have hwg' : ∀ n i, (w n : GradientSpace U q).snd i =ᵐ[μ]
      fun x => deriv (a n) ((v : GradientSpace U q).fst x) * (v : GradientSpace U q).snd i x := by
    simpa only [μ, U, Opens.coe_top, Measure.restrict_univ] using hwg
  have hz : z ∈ energyGraph U X := by
    apply mem_energyGraph_of_componentwise_tendsto U X
      (v := fun n => (w n : GradientSpace U q)) (fun n => (w n).property)
    · exact tendsto_L2_of_contraction_pointwise (v : GradientSpace U q).fst haLip ha0
        hηLip hzero (fun s => tendsto_positivePartApproximation hεpos hε (s - c)) hwf'
    · intro i
      exact tendsto_L2_mul_of_bounded
        (fun n => (ha n).continuous_deriv_one.comp_aestronglyMeasurable
          (Lp.memLp (v : GradientSpace U q).fst).aestronglyMeasurable)
        hbm zero_le_one (fun n => Eventually.of_forall fun x => hab n _) (Eventually.of_forall fun x => hbnd _)
        (Eventually.of_forall fun x => by
          simpa only [a, deriv_comp_sub_const, b, sub_pos] using
            (tendsto_deriv_positivePartApproximation hεpos hε
              ((v : GradientSpace U q).fst x - c)).mul_const _)
        tendsto_const_nhds (fun n => hwg' n i) (hzg i)
  refine ⟨⟨z, hz⟩, ?_, fun i => ?_⟩
  · have H := hηLip.coeFn_compLp hzero (v : GradientSpace U q).fst
    simpa only [z, WithLp.toLp_fst, μ, U, Opens.coe_top, Measure.restrict_univ, Function.comp_def, η] using H
  · have H := hzg i
    simp only [μ, U, Opens.coe_top, Measure.restrict_univ] at H
    apply H.trans
    apply Eventually.of_forall
    intro x
    dsimp [b]
    by_cases hx : c < (v : GradientSpace U q).fst x
    · simp only [ite_eq_left hx, one_mul]
    · simp only [ite_eq_right hx, zero_mul]

/-- Positive parts belong to the energy domain, with derivatives restricted to the strict
positive set. -/
theorem exists_energyGraph_positivePart {N q : ℕ}
    (X : Fin q → (Fin N → ℝ) → (Fin N → ℝ))
    (hX : ∀ i, ContDiff ℝ (⊤ : ℕ∞) (X i)) (v : energyGraph (N := N) ⊤ X) :
    ∃ z : energyGraph (N := N) ⊤ X,
      (z : GradientSpace (N := N) ⊤ q).fst =ᵐ[volume]
        (fun x => max ((v : GradientSpace (N := N) ⊤ q).fst x) 0) ∧
      ∀ i, (z : GradientSpace (N := N) ⊤ q).snd i =ᵐ[volume]
        (fun x => if 0 < (v : GradientSpace (N := N) ⊤ q).fst x
          then (v : GradientSpace (N := N) ⊤ q).snd i x else 0) := by
  simpa only [sub_zero] using exists_energyGraph_positiveLevel X hX v 0 le_rfl

end HeatKernel

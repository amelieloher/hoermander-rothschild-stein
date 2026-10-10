-- Copyright (c) 2026 Scott Armstrong and Amélie Loher. All rights reserved.
-- Released under Apache 2.0 license as described in the file LICENSE.
module

public import HeatKernel.Sobolev.AlmostEverywhereWeightedPoincare
public import HeatKernel.Sobolev.AlmostEverywhereLinearPoincare
public import HeatKernel.Form.GraphForm
public import Mathlib.MeasureTheory.Function.L2Space
import Mathlib.Tactic

/-! # Squared-tent Poincaré for horizontal energy graph elements -/

@[expose] public section
open Set MeasureTheory Metric RothschildStein TopologicalSpace
open scoped ENNReal
namespace HeatKernel.CarnotPoint

/-- Same-ball Poincaré on concentric balls gives the squared-tent inequality
for the value and actual horizontal gradient of an energy graph element. -/
theorem lintegral_tent_sq_sub_weightedMean_le_of_energy_poincare {N q : ℕ}
    (G : HomogeneousGroup N) (hq : q ≤ N) (hqpos : 0 < q)
    (hspan : bracketSpansOn univ (G.horizontalFields hq))
    (hw : ∀ i : Fin q, G.weight (Fin.castLE hq i) = 1)
    (x : CarnotPoint G hq hqpos hspan) {r : ℝ} (hr : 0 < r)
    (v : energyGraph (N := N) ⊤ (G.horizontalFields hq)) {P : ℝ≥0∞}
    (hpoincare : ∀ s : ℝ, 0 < s → s ≤ r →
      (∫⁻ y in ball x s, ENNReal.ofReal (((v : GradientSpace (N := N) ⊤ q).fst y -
        (∫ z in ball x s, (v : GradientSpace (N := N) ⊤ q).fst z ∂volume G hq hqpos hspan) /
          (volume G hq hqpos hspan).real (ball x s)) ^ 2) ∂volume G hq hqpos hspan) ≤
        P * ENNReal.ofReal s ^ 2 * ∫⁻ y in ball x s, ENNReal.ofReal (∑ i, ((v : GradientSpace (N := N) ⊤ q).snd i y) ^ 2) ∂volume G hq hqpos hspan) :
    (∫⁻ y, ENNReal.ofReal (max (1 - dist x y / r) 0 ^ 2) *
      ENNReal.ofReal (((v : GradientSpace (N := N) ⊤ q).fst y - Sobolev.weightedMean (volume G hq hqpos hspan)
        (fun z => max (1 - dist x z / r) 0 ^ 2) (fun y => (v : GradientSpace (N := N) ⊤ q).fst y)) ^ 2) ∂volume G hq hqpos hspan) ≤
      (3 * (P * ENNReal.ofReal (r / 2) ^ 2) +
        ENNReal.ofReal (1 + (2 : ℝ) ^ G.homogeneousDimension) * P * ENNReal.ofReal r ^ 2) *
        ∫⁻ y, ENNReal.ofReal (max (1 - dist x y / r) 0 ^ 2) * ENNReal.ofReal (∑ i, ((v : GradientSpace (N := N) ⊤ q).snd i y) ^ 2) ∂volume G hq hqpos hspan := by
  have hf : MemLp (fun y : CarnotPoint G hq hqpos hspan =>
      (v : GradientSpace (N := N) ⊤ q).fst y) 2 (volume G hq hqpos hspan) := by
    change MemLp ((v : GradientSpace (N := N) ⊤ q).fst : (Fin N → ℝ) → ℝ) 2 MeasureTheory.volume
    simpa only [Opens.coe_top, Measure.restrict_univ] using
      Lp.memLp (v : GradientSpace (N := N) ⊤ q).fst
  have hgrad (i : Fin q) : MemLp (fun y : CarnotPoint G hq hqpos hspan =>
      (v : GradientSpace (N := N) ⊤ q).snd i y) 2 (volume G hq hqpos hspan) := by
    change MemLp ((v : GradientSpace (N := N) ⊤ q).snd i : (Fin N → ℝ) → ℝ) 2 MeasureTheory.volume
    simpa only [Opens.coe_top, Measure.restrict_univ] using
      Lp.memLp ((v : GradientSpace (N := N) ⊤ q).snd i)
  have hm : AEStronglyMeasurable (fun y : CarnotPoint G hq hqpos hspan =>
      ∑ i, ((v : GradientSpace (N := N) ⊤ q).snd i y) ^ 2) (volume G hq hqpos hspan) := by
    exact Finset.aestronglyMeasurable_fun_sum Finset.univ
      (fun i _ => (hgrad i).aestronglyMeasurable.pow 2)
  have hg := ENNReal.continuous_ofReal.measurable.comp_aemeasurable hm.aemeasurable
  have hball : ball x r = horizontalBall (G.horizontalFields hq) x r := by
    ext y
    rw [mem_ball, ← edist_lt_ofReal, edist_comm, edist_eq]
    rfl
  have hfinite : (volume G hq hqpos hspan) (ball x r) < ⊤ := by
    rw [hball]
    exact volume_horizontalBall_lt_top G hq hqpos hspan hw x hr.le
  let : IsFiniteMeasure ((volume G hq hqpos hspan).restrict (ball x r)) :=
    isFiniteMeasure_restrict.mpr hfinite.ne
  exact lintegral_tent_sq_sub_weightedMean_le_of_ae_poincare G hq hqpos hspan hw x hr
    hf.aestronglyMeasurable.aemeasurable (MemLp.integrable (by norm_num) (hf.restrict _))
    (hf.restrict _).integrable_sq hg hpoincare

/-- Same-ball Poincaré on concentric balls gives the linear-tent inequality
for the value and actual horizontal gradient of an energy graph element. -/
theorem lintegral_tent_sub_weightedMean_le_of_energy_poincare {N q : ℕ}
    (G : HomogeneousGroup N) (hq : q ≤ N) (hqpos : 0 < q)
    (hspan : bracketSpansOn univ (G.horizontalFields hq))
    (hw : ∀ i : Fin q, G.weight (Fin.castLE hq i) = 1)
    (x : CarnotPoint G hq hqpos hspan) {r : ℝ} (hr : 0 < r)
    (v : energyGraph (N := N) ⊤ (G.horizontalFields hq)) {P : ℝ≥0∞}
    (hpoincare : ∀ s : ℝ, 0 < s → s ≤ r →
      (∫⁻ y in ball x s, ENNReal.ofReal (((v : GradientSpace (N := N) ⊤ q).fst y -
        (∫ z in ball x s, (v : GradientSpace (N := N) ⊤ q).fst z ∂volume G hq hqpos hspan) /
          (volume G hq hqpos hspan).real (ball x s)) ^ 2) ∂volume G hq hqpos hspan) ≤
        P * ENNReal.ofReal s ^ 2 * ∫⁻ y in ball x s, ENNReal.ofReal (∑ i, ((v : GradientSpace (N := N) ⊤ q).snd i y) ^ 2) ∂volume G hq hqpos hspan) :
    (∫⁻ y, ENNReal.ofReal (max (1 - dist x y / r) 0) *
      ENNReal.ofReal (((v : GradientSpace (N := N) ⊤ q).fst y - Sobolev.weightedMean (volume G hq hqpos hspan)
        (fun z => max (1 - dist x z / r) 0) (fun y => (v : GradientSpace (N := N) ⊤ q).fst y)) ^ 2) ∂volume G hq hqpos hspan) ≤
      ((P * ENNReal.ofReal (r / 2) ^ 2) +
        ENNReal.ofReal (1 + (2 : ℝ) ^ G.homogeneousDimension) * P * ENNReal.ofReal r ^ 2) *
        ∫⁻ y, ENNReal.ofReal (max (1 - dist x y / r) 0) * ENNReal.ofReal (∑ i, ((v : GradientSpace (N := N) ⊤ q).snd i y) ^ 2) ∂volume G hq hqpos hspan := by
  have hf : MemLp (fun y : CarnotPoint G hq hqpos hspan =>
      (v : GradientSpace (N := N) ⊤ q).fst y) 2 (volume G hq hqpos hspan) := by
    change MemLp ((v : GradientSpace (N := N) ⊤ q).fst : (Fin N → ℝ) → ℝ) 2 MeasureTheory.volume
    simpa only [Opens.coe_top, Measure.restrict_univ] using
      Lp.memLp (v : GradientSpace (N := N) ⊤ q).fst
  have hgrad (i : Fin q) : MemLp (fun y : CarnotPoint G hq hqpos hspan =>
      (v : GradientSpace (N := N) ⊤ q).snd i y) 2 (volume G hq hqpos hspan) := by
    change MemLp ((v : GradientSpace (N := N) ⊤ q).snd i : (Fin N → ℝ) → ℝ) 2 MeasureTheory.volume
    simpa only [Opens.coe_top, Measure.restrict_univ] using
      Lp.memLp ((v : GradientSpace (N := N) ⊤ q).snd i)
  have hm : AEStronglyMeasurable (fun y : CarnotPoint G hq hqpos hspan =>
      ∑ i, ((v : GradientSpace (N := N) ⊤ q).snd i y) ^ 2) (volume G hq hqpos hspan) := by
    exact Finset.aestronglyMeasurable_fun_sum Finset.univ
      (fun i _ => (hgrad i).aestronglyMeasurable.pow 2)
  have hg := ENNReal.continuous_ofReal.measurable.comp_aemeasurable hm.aemeasurable
  have hball : ball x r = horizontalBall (G.horizontalFields hq) x r := by
    ext y
    rw [mem_ball, ← edist_lt_ofReal, edist_comm, edist_eq]
    rfl
  have hfinite : (volume G hq hqpos hspan) (ball x r) < ⊤ := by
    rw [hball]
    exact volume_horizontalBall_lt_top G hq hqpos hspan hw x hr.le
  let : IsFiniteMeasure ((volume G hq hqpos hspan).restrict (ball x r)) :=
    isFiniteMeasure_restrict.mpr hfinite.ne
  exact lintegral_tent_sub_weightedMean_le_of_ae_poincare G hq hqpos hspan hw x hr
    hf.aestronglyMeasurable.aemeasurable (MemLp.integrable (by norm_num) (hf.restrict _))
    (hf.restrict _).integrable_sq hg hpoincare

end HeatKernel.CarnotPoint

-- Copyright (c) 2026 Scott Armstrong and Amélie Loher. All rights reserved.
-- Released under Apache 2.0 license as described in the file LICENSE.
module

public import HeatKernel.Sobolev.EnergyWeightedPoincare
public import HeatKernel.Sobolev.LocalWeightedCongruence
public import HeatKernel.Bridge.LocalSobolev
public import RothschildStein.Definitions.HomogeneousGroup.horizontalFields_contDiff
import Mathlib.Tactic
import all HeatKernel.Geometry.CarnotPoint
import all Mathlib.Basic.Real.Basic

/-! # Linear-tent Poincaré for local horizontal energy functions -/

@[expose] public section
open Set MeasureTheory Metric RothschildStein TopologicalSpace
open scoped ENNReal
namespace HeatKernel.CarnotPoint

/-- Same-ball Poincaré gives the linear-tent inequality for a local energy
function and its supplied weak gradient, using a compact interior neighborhood. -/
theorem lintegral_tent_sub_weightedMean_le_of_local_energy_poincare {N q : ℕ}
    (G : HomogeneousGroup N) (hq : q ≤ N) (hqpos : 0 < q)
    (hspan : bracketSpansOn univ (G.horizontalFields hq))
    (hw : ∀ i : Fin q, G.weight (Fin.castLE hq i) = 1)
    (x : CarnotPoint G hq hqpos hspan) {r : ℝ} (hr : 0 < r)
    (U V : Opens (Fin N → ℝ))
    (hVc : IsCompact (closure (V : Set (Fin N → ℝ))))
    (hVU : closure (V : Set (Fin N → ℝ)) ⊆ (U : Set (Fin N → ℝ)))
    (hBV : horizontalBall (G.horizontalFields hq) x r ⊆ (V : Set (Fin N → ℝ)))
    (f : (Fin N → ℝ) → ℝ) (g : Fin q → (Fin N → ℝ) → ℝ)
    (hf : MemLocalEnergy U (G.horizontalFields hq) f)
    (hg : ∀ i, hasWeakWordDeriv (G.horizontalFields hq) U [i] f (g i)) {P : ℝ≥0∞}
    (hpoincare : ∀ s : ℝ, 0 < s → s ≤ r →
      (∫⁻ y in ball x s, ENNReal.ofReal ((f y -
        (∫ z in ball x s, f z ∂volume G hq hqpos hspan) /
          (volume G hq hqpos hspan).real (ball x s)) ^ 2) ∂volume G hq hqpos hspan) ≤
        P * ENNReal.ofReal s ^ 2 * ∫⁻ y in ball x s, ENNReal.ofReal (∑ i, (g i y) ^ 2) ∂volume G hq hqpos hspan) :
    (∫⁻ y, ENNReal.ofReal (max (1 - dist x y / r) 0) *
      ENNReal.ofReal ((f y - Sobolev.weightedMean (volume G hq hqpos hspan)
        (fun z => max (1 - dist x z / r) 0) (fun y => f y)) ^ 2) ∂volume G hq hqpos hspan) ≤
      ((P * ENNReal.ofReal (r / 2) ^ 2) +
        ENNReal.ofReal (1 + (2 : ℝ) ^ G.homogeneousDimension) * P * ENNReal.ofReal r ^ 2) *
        ∫⁻ y, ENNReal.ofReal (max (1 - dist x y / r) 0) * ENNReal.ofReal (∑ i, (g i y) ^ 2) ∂volume G hq hqpos hspan := by
  obtain ⟨v, hv⟩ := hf.2 V hVc hVU
  have hball : ball x r = horizontalBall (G.horizontalFields hq) x r := by
    ext y
    rw [mem_ball, ← edist_lt_ofReal, edist_comm, edist_eq]
    rfl
  have hBsub : ball x r ⊆ (V : Set (Fin N → ℝ)) := by
    rw [hball]
    exact hBV
  have hvf : (fun y : CarnotPoint G hq hqpos hspan => (v : GradientSpace (N := N) ⊤ q).fst y)
      =ᵐ[(volume G hq hqpos hspan).restrict (ball x r)] (fun y => f y) :=
    ae_restrict_of_ae_restrict_of_subset hBsub hv
  have hvg (i : Fin q) : (fun y : CarnotPoint G hq hqpos hspan =>
      (v : GradientSpace (N := N) ⊤ q).snd i y) =ᵐ[
      (volume G hq hqpos hspan).restrict (ball x r)] (fun y => g i y) := by
    rw [hball]
    have H := energyGradient_eq_of_local_weak_derivative U V (subset_closure.trans hVU)
      (G.horizontalFields hq) (G.horizontalFields_contDiff hq) v hv i (hg i)
    have H' : ((v : GradientSpace (N := N) ⊤ q).snd i : (Fin N → ℝ) → ℝ) =ᵐ[
        (MeasureTheory.volume : Measure (Fin N → ℝ)).restrict
          (horizontalBall (G.horizontalFields hq) x r)] g i := by
      change ((v : GradientSpace (N := N) ⊤ q).snd i : (Fin N → ℝ) → ℝ) =ᵐ[
        (MeasureTheory.volume : Measure (Fin N → ℝ)).restrict (V : Set (Fin N → ℝ))] g i at H
      exact ae_restrict_of_ae_restrict_of_subset hBV H
    convert H' using 1 <;> rfl

  have hE : (fun y : CarnotPoint G hq hqpos hspan =>
      ENNReal.ofReal (∑ i, ((v : GradientSpace (N := N) ⊤ q).snd i y) ^ 2)) =ᵐ[
        (volume G hq hqpos hspan).restrict (ball x r)]
      (fun y => ENNReal.ofReal (∑ i, (g i y) ^ 2)) := by
    filter_upwards [ae_all_iff.mpr hvg] with y hy
    simp only [fun i => hy i]
  have hpi : ∀ s : ℝ, 0 < s → s ≤ r →
      (∫⁻ y in ball x s, ENNReal.ofReal (((v : GradientSpace (N := N) ⊤ q).fst y -
        (∫ z in ball x s, (v : GradientSpace (N := N) ⊤ q).fst z ∂volume G hq hqpos hspan) /
          (volume G hq hqpos hspan).real (ball x s)) ^ 2) ∂volume G hq hqpos hspan) ≤
        P * ENNReal.ofReal s ^ 2 * ∫⁻ y in ball x s,
          ENNReal.ofReal (∑ i, ((v : GradientSpace (N := N) ⊤ q).snd i y) ^ 2)
            ∂volume G hq hqpos hspan := by
    intro s hs hsr
    have hval := ae_restrict_of_ae_restrict_of_subset (ball_subset_ball hsr) hvf
    have henergy := ae_restrict_of_ae_restrict_of_subset (ball_subset_ball hsr) hE
    rw [Sobolev.lintegral_sub_setAverage_sq_congr_ae (ball x s) hval,
      lintegral_congr_ae henergy]
    exact hpoincare s hs hsr
  have H := lintegral_tent_sub_weightedMean_le_of_energy_poincare G hq hqpos hspan hw x hr v hpi
  have hweight : Function.support (fun y : CarnotPoint G hq hqpos hspan =>
      max (1 - dist x y / r) 0) ⊆ ball x r := by
    intro y hy
    by_contra hn
    have hd : r ≤ dist x y := by simpa only [mem_ball, not_lt, dist_comm y x] using hn
    have hdiv : 1 ≤ dist x y / r := (le_div_iff₀ hr).mpr (by simpa only [one_mul] using hd)
    have hz : max (1 - dist x y / r) 0 = 0 := max_eq_right (by linarith)
    exact hy (by simp [hz])
  rw [Sobolev.lintegral_weighted_variance_congr_ae_restrict_support _ hweight hvf,
    Sobolev.lintegral_weight_mul_congr_ae_restrict_support _ hweight hE] at H
  exact H

end HeatKernel.CarnotPoint

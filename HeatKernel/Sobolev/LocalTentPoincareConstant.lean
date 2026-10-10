-- Copyright (c) 2026 Scott Armstrong and Amélie Loher. All rights reserved.
-- Released under Apache 2.0 license as described in the file LICENSE.
module

public import HeatKernel.Sobolev.InteriorEnergyWeightedPoincare
public import HeatKernel.Sobolev.InteriorEnergyLinearPoincare
public import HeatKernel.Sobolev.TentPoincareCoefficients
import Mathlib.Tactic
import all HeatKernel.Geometry.CarnotPoint

/-! # One constant for the two interior tent Poincaré inequalities -/

@[expose] public section
open Set MeasureTheory Metric RothschildStein TopologicalSpace
open scoped ENNReal
namespace HeatKernel.CarnotPoint

/-- Both distance-tent weights satisfy the local energy Poincaré estimate with
the common coefficient determined only by the dimension and the Poincaré constant. -/
theorem lintegral_tent_pow_sub_weightedMean_le_of_local_poincare {N q : ℕ}
    (G : HomogeneousGroup N) (hq : q ≤ N) (hqpos : 0 < q)
    (hspan : bracketSpansOn univ (G.horizontalFields hq))
    (hw : ∀ i : Fin q, G.weight (Fin.castLE hq i) = 1)
    (x : CarnotPoint G hq hqpos hspan) {r : ℝ} (hr : 0 < r)
    (U : Opens (Fin N → ℝ))
    (hroom : {y : Fin N → ℝ | horizontalL2Distance (G.horizontalFields hq) x y ≤
      ENNReal.ofReal r} ⊆ (U : Set (Fin N → ℝ)))
    (f : (Fin N → ℝ) → ℝ) (g : Fin q → (Fin N → ℝ) → ℝ)
    (hf : MemLocalEnergy U (G.horizontalFields hq) f)
    (hg : ∀ i, hasWeakWordDeriv (G.horizontalFields hq) U [i] f (g i))
    {P : ℝ} (hP : 0 < P) (α : ℕ) (hα : α = 1 ∨ α = 2)
    (hpoincare : ∀ s : ℝ, 0 < s → s ≤ r →
      (∫⁻ y in ball x s, ENNReal.ofReal ((f y -
        (∫ z in ball x s, f z ∂volume G hq hqpos hspan) /
          (volume G hq hqpos hspan).real (ball x s)) ^ 2) ∂volume G hq hqpos hspan) ≤
        ENNReal.ofReal P * ENNReal.ofReal s ^ 2 * ∫⁻ y in ball x s, ENNReal.ofReal (∑ i, (g i y) ^ 2) ∂volume G hq hqpos hspan) :
    (∫⁻ y, ENNReal.ofReal (max (1 - dist x y / r) 0 ^ α) *
      ENNReal.ofReal ((f y - Sobolev.weightedMean (volume G hq hqpos hspan)
        (fun z => max (1 - dist x z / r) 0 ^ α) (fun y => f y)) ^ 2) ∂volume G hq hqpos hspan) ≤
      ENNReal.ofReal (P * (((2 : ℝ) ^ G.homogeneousDimension + 7 / 4) * r ^ 2)) *
        ∫⁻ y, ENNReal.ofReal (max (1 - dist x y / r) 0 ^ α) * ENNReal.ofReal (∑ i, (g i y) ^ 2) ∂volume G hq hqpos hspan := by
  rcases hα with rfl | rfl
  · have H := lintegral_tent_sub_weightedMean_le_of_interior_energy_poincare
      G hq hqpos hspan hw x hr U hroom f g hf hg hpoincare
    rw [Sobolev.linear_tent_poincare_coefficient_eq G.homogeneousDimension
      (ENNReal.ofReal P) hr.le, ← ENNReal.ofReal_mul hP.le] at H
    have hc : ENNReal.ofReal (P * (((2 : ℝ) ^ G.homogeneousDimension + 5 / 4) * r ^ 2)) ≤
        ENNReal.ofReal (P * (((2 : ℝ) ^ G.homogeneousDimension + 7 / 4) * r ^ 2)) := by
      apply ENNReal.ofReal_le_ofReal
      gcongr
      norm_num
    simpa only [pow_one] using H.trans (mul_le_mul' hc le_rfl)
  · have H := lintegral_tent_sq_sub_weightedMean_le_of_interior_energy_poincare
      G hq hqpos hspan hw x hr U hroom f g hf hg hpoincare
    rw [Sobolev.squared_tent_poincare_coefficient_eq G.homogeneousDimension
      (ENNReal.ofReal P) hr.le, ← ENNReal.ofReal_mul hP.le] at H
    exact H

end HeatKernel.CarnotPoint

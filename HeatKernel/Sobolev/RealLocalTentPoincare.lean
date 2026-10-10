-- Copyright (c) 2026 Scott Armstrong and Amélie Loher. All rights reserved.
-- Released under Apache 2.0 license as described in the file LICENSE.
module

public import HeatKernel.Sobolev.LocalTentPoincareConstant
public import HeatKernel.Sobolev.LocalTentEnergyMoments
public import HeatKernel.Sobolev.RealWeightedInequality
import Mathlib.Tactic
import all HeatKernel.Geometry.CarnotPoint

/-! # Real-integral tent Poincaré on local horizontal energy functions -/

@[expose] public section
open Set MeasureTheory Metric RothschildStein TopologicalSpace
open scoped ENNReal
namespace HeatKernel.CarnotPoint

/-- Both tent powers satisfy the real-integral local Poincaré estimate with the
mean normalized by the total tent mass and the common dimension-dependent constant. -/
theorem integral_tent_pow_sub_mean_le_of_local_poincare {N q : ℕ}
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
    let w : CarnotPoint G hq hqpos hspan → ℝ := fun y => max (1 - dist x y / r) 0 ^ α
    let m := (∫ y in ball x r, w y * f y ∂volume G hq hqpos hspan) /
      (∫ y, w y ∂volume G hq hqpos hspan)
    (∫ y in ball x r, w y * (f y - m) ^ 2 ∂volume G hq hqpos hspan) ≤
      (P * ((2 : ℝ) ^ G.homogeneousDimension + 7 / 4)) * r ^ 2 *
        ∫ y in ball x r, w y * ∑ i, (g i y) ^ 2 ∂volume G hq hqpos hspan := by
  let w : CarnotPoint G hq hqpos hspan → ℝ := fun y => max (1 - dist x y / r) 0 ^ α
  change (∫ y in ball x r, w y * (f y -
    (∫ z in ball x r, w z * f z ∂volume G hq hqpos hspan) /
      (∫ z, w z ∂volume G hq hqpos hspan)) ^ 2 ∂volume G hq hqpos hspan) ≤
    (P * ((2 : ℝ) ^ G.homogeneousDimension + 7 / 4)) * r ^ 2 *
      ∫ y in ball x r, w y * ∑ i, (g i y) ^ 2 ∂volume G hq hqpos hspan
  have hαpos : 0 < α := by rcases hα with rfl | rfl <;> norm_num
  obtain ⟨_, hwn, _, hsupport⟩ := Sobolev.distance_tent_pow_properties x hr hαpos
  have hzero (y : CarnotPoint G hq hqpos hspan) (hy : y ∉ ball x r) : w y = 0 := by
    by_contra hn
    exact hy (hsupport hn)
  obtain ⟨hi, hj⟩ := integrable_local_tent_energy_moments G hq hqpos hspan hw x hr
    U hroom f g hf hg hαpos
  have H := lintegral_tent_pow_sub_weightedMean_le_of_local_poincare
    G hq hqpos hspan hw x hr U hroom f g hf hg hP α hα hpoincare
  have hreal := Sobolev.integral_weighted_variance_le_of_lintegral
    (w := w) (f := fun y => f y) (e := fun y => ∑ i, (g i y) ^ 2)
    hwn (fun y => Finset.sum_nonneg (fun i _ => sq_nonneg (g i y)))
    (by positivity : 0 ≤ P * (((2 : ℝ) ^ G.homogeneousDimension + 7 / 4) * r ^ 2))
    (hi (Sobolev.weightedMean (volume G hq hqpos hspan) w (fun y => f y))) hj H
  have hmean : Sobolev.weightedMean (volume G hq hqpos hspan) w (fun y => f y) =
      (∫ y in ball x r, w y * f y ∂volume G hq hqpos hspan) /
        (∫ y, w y ∂volume G hq hqpos hspan) := by
    unfold Sobolev.weightedMean
    congr 1
    symm
    apply setIntegral_eq_integral_of_forall_compl_eq_zero
    intro y hy
    rw [hzero y hy, zero_mul]
  have hleft : (∫ y in ball x r, w y *
      (f y - Sobolev.weightedMean (volume G hq hqpos hspan) w (fun y => f y)) ^ 2
        ∂volume G hq hqpos hspan) =
      ∫ y, w y * (f y - Sobolev.weightedMean (volume G hq hqpos hspan) w (fun y => f y)) ^ 2
        ∂volume G hq hqpos hspan := by
    apply setIntegral_eq_integral_of_forall_compl_eq_zero
    intro y hy
    rw [hzero y hy, zero_mul]
  have hright : (∫ y in ball x r, w y * ∑ i, (g i y) ^ 2 ∂volume G hq hqpos hspan) =
      ∫ y, w y * ∑ i, (g i y) ^ 2 ∂volume G hq hqpos hspan := by
    apply setIntegral_eq_integral_of_forall_compl_eq_zero
    intro y hy
    rw [hzero y hy, zero_mul]
  rw [← hmean, hleft, hright]
  have hcoef : (P * ((2 : ℝ) ^ G.homogeneousDimension + 7 / 4)) * r ^ 2 =
      P * (((2 : ℝ) ^ G.homogeneousDimension + 7 / 4) * r ^ 2) := by ring
  rw [hcoef]
  exact hreal

end HeatKernel.CarnotPoint

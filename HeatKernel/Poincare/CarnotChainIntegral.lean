-- Copyright (c) 2026 Scott Armstrong and Amélie Loher. All rights reserved.
-- Released under Apache 2.0 license as described in the file LICENSE.
module

public import HeatKernel.Poincare.SimplePathIntegral
public import HeatKernel.Poincare.LocalChainCost
public import HeatKernel.Poincare.CoverChain
public import HeatKernel.Poincare.CarnotBallVolume

/-! Local power-integral estimates for Whitney chains in horizontal balls. -/

@[expose] public section
set_option autoImplicit false
set_option relaxedAutoImplicit false
noncomputable section
open Set Metric MeasureTheory RothschildStein
open scoped NNReal ENNReal BigOperators Classical

namespace HeatKernel

/-- The local twentyfold oscillation bounds and neighboring-average estimates give
the power-integral chain bound on the starting ball's fivefold dilate. -/
theorem lintegral_abs_sub_rpow_le_horizontal_chain_cost {N q : ℕ} {ι : Type*}
    (G : HomogeneousGroup N) (hq : q ≤ N) (hqpos : 0 < q)
    (hspan : bracketSpansOn univ (G.horizontalFields hq))
    (hw : ∀ k : Fin q, G.weight (Fin.castLE hq k) = 1)
    (z : ι → CarnotPoint G hq hqpos hspan) (a c : ι → ℝ) (h : ι → ℝ≥0)
    (ha : ∀ k, 0 < a k) {p : ℝ} (hp : 1 ≤ p) (u : (Fin N → ℝ) → ℝ)
    (hlocal : ∀ k, eLpNorm (fun y => u y - c k) (ENNReal.ofReal p)
      (volume.restrict (horizontalBall (G.horizontalFields hq) (z k) (20 * a k))) ≤
      ENNReal.ofReal (((2 : ℝ) ^ G.homogeneousDimension) ^ (1 / p) * (3 * (20 * a k))) *
        volume (horizontalBall (G.horizontalFields hq) (z k) (a k)) ^ (1 / p) * h k)
    (hedge : ∀ k l, (ball (z k) (5 * a k) ∩ ball (z l) (5 * a l)).Nonempty →
      |c k - c l| ≤ (60 * (((2 : ℝ) ^ G.homogeneousDimension) ^ (1 / p)) ^ 2) *
        (a k * (h k : ℝ) + a l * (h l : ℝ)))
    {i j : ι} (w : (intersectionGraph (fun k => ball (z k) (5 * a k))).Walk i j)
    (hpath : w.IsPath)
    (hf : AEStronglyMeasurable (fun y => u y - c j)
      (volume.restrict (horizontalBall (G.horizontalFields hq) (z i) (5 * a i)))) :
    (∫⁻ y in horizontalBall (G.horizontalFields hq) (z i) (5 * a i),
      ENNReal.ofReal (|u y - c j| ^ p)) ≤
      ENNReal.ofReal ((3 * (60 * (((2 : ℝ) ^ G.homogeneousDimension) ^ (1 / p)) ^ 2)) ^ p) *
        ENNReal.ofReal ((5 : ℝ) ^ G.homogeneousDimension) *
        volume (horizontalBall (G.horizontalFields hq) (z i) (a i)) *
        ENNReal.ofReal ((∑ k ∈ w.support.toFinset, a k * (h k : ℝ)) ^ p) := by
  let K := 60 * (((2 : ℝ) ^ G.homogeneousDimension) ^ (1 / p)) ^ 2
  let L := 60 * ((2 : ℝ) ^ G.homogeneousDimension) ^ (1 / p)
  have hp0 : 0 < p := lt_of_lt_of_le zero_lt_one hp
  have hK : 0 ≤ K := by dsimp only [K]; positivity
  have hmono : ∀ (s t : ℝ), s ≤ t → ∀ k,
      horizontalBall (G.horizontalFields hq) (z k) s ⊆
        horizontalBall (G.horizontalFields hq) (z k) t := by
    intro s t hst k y hy
    exact lt_of_lt_of_le hy (ENNReal.ofReal_le_ofReal hst)
  have hfirst := hlocal i
  rw [show ((2 : ℝ) ^ G.homogeneousDimension) ^ (1 / p) * (3 * (20 * a i)) =
    L * a i by dsimp only [L]; ring] at hfirst
  have hn := eLpNorm_restrict_le_normalized_chain_cost volume (fun y => u y - c i)
    (hmono (a i) (5 * a i) (by linarith [ha i]) i)
    (hmono (5 * a i) (20 * a i) (by linarith [ha i]) i)
    hp0 (ha i).le hK (local_homogeneous_coefficient_le_edge_coefficient
      G.homogeneousDimension hp0) (h i) hfirst
  have hi := lintegral_abs_sub_rpow_le_simple_path_cost volume u
    (horizontalBall (G.horizontalFields hq) (z i) (5 * a i))
    (intersectionGraph (fun k => ball (z k) (5 * a k))) c
    (fun k => a k * (h k : ℝ)) (fun k => mul_nonneg (ha k).le (h k).2) hK
    (fun k l hkl => hedge k l hkl.2) w hpath hp hf hn
  have hv : volume (horizontalBall (G.horizontalFields hq) (z i) (5 * a i)) =
      ENNReal.ofReal ((5 : ℝ) ^ G.homogeneousDimension) *
        volume (horizontalBall (G.horizontalFields hq) (z i) (a i)) := by
    rw [volume_horizontalBall G hq hw (z i) (mul_pos (by norm_num) (ha i)),
      volume_horizontalBall G hq hw (z i) (ha i), mul_pow,
      ENNReal.ofReal_mul (by positivity)]
    ac_rfl
  rw [hv] at hi
  exact hi.trans_eq (by dsimp only [K]; ac_rfl)

end HeatKernel

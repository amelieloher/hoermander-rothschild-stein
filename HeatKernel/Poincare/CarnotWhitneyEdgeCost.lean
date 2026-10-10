-- Copyright (c) 2026 Scott Armstrong and Amélie Loher. All rights reserved.
-- Released under Apache 2.0 license as described in the file LICENSE.
module

public import HeatKernel.Poincare.WhitneyEdgeCost
public import HeatKernel.Poincare.FiniteEdgeCost

/-! Finite real edge bounds for Whitney averages on a Carnot group. -/

@[expose] public section
set_option autoImplicit false
set_option relaxedAutoImplicit false
noncomputable section
open Set Metric MeasureTheory RothschildStein
open scoped NNReal ENNReal

namespace HeatKernel

/-- The neighboring-ball oscillation bounds imply the real edge estimate used when
telescoping Whitney averages. -/
theorem abs_sub_le_boundaryBall_edge_cost {N q : ℕ}
    (G : HomogeneousGroup N) (hq : q ≤ N) (hqpos : 0 < q)
    (hspan : bracketSpansOn univ (G.horizontalFields hq))
    (hw : ∀ i : Fin q, G.weight (Fin.castLE hq i) = 1)
    {x z w : CarnotPoint G hq hqpos hspan} {r κ a b p : ℝ} (hr : 0 < r) (hκ : 80 < κ)
    (hz : z ∈ ball x r) (hwball : w ∈ ball x r) (hp : 1 ≤ p)
    (haeq : a = infDist z (ball x r)ᶜ / κ) (hbeq : b = infDist w (ball x r)ᶜ / κ)
    (hmeet : (ball z (5 * a) ∩ ball w (5 * b)).Nonempty)
    (u : (Fin N → ℝ) → ℝ) (c d : ℝ) (h₁ h₂ : ℝ≥0)
    (hfirst : eLpNorm (fun y => u y - c) (ENNReal.ofReal p)
      (volume.restrict (horizontalBall (G.horizontalFields hq) z (20 * a))) ≤
      ENNReal.ofReal (((2 : ℝ) ^ G.homogeneousDimension) ^ (1 / p) * (3 * (20 * a))) *
        volume (horizontalBall (G.horizontalFields hq) z a) ^ (1 / p) * h₁)
    (hsecond : eLpNorm (fun y => u y - d) (ENNReal.ofReal p)
      (volume.restrict (horizontalBall (G.horizontalFields hq) w (20 * b))) ≤
      ENNReal.ofReal (((2 : ℝ) ^ G.homogeneousDimension) ^ (1 / p) * (3 * (20 * b))) *
        volume (horizontalBall (G.horizontalFields hq) w b) ^ (1 / p) * h₂) :
    |c - d| ≤ (60 * (((2 : ℝ) ^ G.homogeneousDimension) ^ (1 / p)) ^ 2) *
      (a * (h₁ : ℝ) + b * (h₂ : ℝ)) := by
  have hp0 : 0 < p := lt_of_lt_of_le zero_lt_one hp
  have hκ0 : 0 ≤ κ := by linarith
  have ha : 0 ≤ a := by rw [haeq]; exact div_nonneg infDist_nonneg hκ0
  have hb : 0 ≤ b := by rw [hbeq]; exact div_nonneg infDist_nonneg hκ0
  have hh := ofReal_abs_sub_le_boundaryBall_edge_cost G hq hqpos hspan hw hr hκ
    hz hwball hp haeq hbeq hmeet u c d h₁ h₂ hfirst hsecond
  rw [homogeneous_edge_coefficient_eq_ofReal G.homogeneousDimension hp0] at hh
  exact abs_sub_le_of_nonnegative_weighted_edge_cost ha hb (by positivity) h₁ h₂ hh

end HeatKernel

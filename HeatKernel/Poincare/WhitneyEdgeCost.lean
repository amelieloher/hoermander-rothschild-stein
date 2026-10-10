-- Copyright (c) 2026 Scott Armstrong and Amélie Loher. All rights reserved.
-- Released under Apache 2.0 license as described in the file LICENSE.
module

public import HeatKernel.Poincare.CarnotWhitneyMeanComparison

/-! Explicit weighted edge costs for neighboring Whitney averaging constants. -/

@[expose] public section
set_option autoImplicit false
set_option relaxedAutoImplicit false
noncomputable section
open Set Metric MeasureTheory RothschildStein
open scoped NNReal ENNReal

namespace HeatKernel

/-- The local weak Poincaré oscillation bounds give an edge cost proportional to the
sum of radius times normalized gradient cost, with the homogeneous comparison factor. -/
theorem ofReal_abs_sub_le_boundaryBall_edge_cost {N q : ℕ}
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
    ENNReal.ofReal |c - d| ≤
      (((2 : ℝ≥0∞) ^ G.homogeneousDimension) ^ (1 / p) *
        ENNReal.ofReal (60 * ((2 : ℝ) ^ G.homogeneousDimension) ^ (1 / p))) *
          (ENNReal.ofReal a * h₁ + ENNReal.ofReal b * h₂) := by
  let C := ((2 : ℝ) ^ G.homogeneousDimension) ^ (1 / p)
  let e₁ := ENNReal.ofReal (C * (3 * (20 * a))) * h₁
  let e₂ := ENNReal.ofReal (C * (3 * (20 * b))) * h₂
  have hp0 : 0 ≤ p := le_trans zero_le_one hp
  have hfirst' : eLpNorm (fun y => u y - c) (ENNReal.ofReal p)
      (volume.restrict (horizontalBall (G.horizontalFields hq) z (20 * a))) ≤
      e₁ * volume (horizontalBall (G.horizontalFields hq) z a) ^ (1 / (ENNReal.ofReal p).toReal) := by
    rw [ENNReal.toReal_ofReal hp0]
    exact hfirst.trans_eq (by dsimp only [e₁, C]; ac_rfl)
  have hsecond' : eLpNorm (fun y => u y - d) (ENNReal.ofReal p)
      (volume.restrict (horizontalBall (G.horizontalFields hq) w (20 * b))) ≤
      e₂ * volume (horizontalBall (G.horizontalFields hq) w b) ^ (1 / (ENNReal.ofReal p).toReal) := by
    rw [ENNReal.toReal_ofReal hp0]
    exact hsecond.trans_eq (by dsimp only [e₂, C]; ac_rfl)
  have hh := ofReal_abs_sub_le_of_horizontal_boundaryBall_oscillation_bounds G hq hqpos hspan hw
    hr hκ hz hwball haeq hbeq hmeet u c d
    (by simpa only [ENNReal.ofReal_one] using ENNReal.ofReal_le_ofReal hp)
    ENNReal.ofReal_ne_top e₁ e₂ hfirst' hsecond'
  rw [ENNReal.toReal_ofReal hp0] at hh
  have hC0 : 0 ≤ 60 * C := mul_nonneg (by norm_num) (Real.rpow_nonneg (by positivity) _)
  have hCa : ENNReal.ofReal (C * (3 * (20 * a))) = ENNReal.ofReal (60 * C) * ENNReal.ofReal a := by
    rw [show C * (3 * (20 * a)) = (60 * C) * a by ring, ENNReal.ofReal_mul hC0]
  have hCb : ENNReal.ofReal (C * (3 * (20 * b))) = ENNReal.ofReal (60 * C) * ENNReal.ofReal b := by
    rw [show C * (3 * (20 * b)) = (60 * C) * b by ring, ENNReal.ofReal_mul hC0]
  calc
    ENNReal.ofReal |c - d| ≤ ((2 : ℝ≥0∞) ^ G.homogeneousDimension) ^ (1 / p) * (e₁ + e₂) := hh
    _ = (((2 : ℝ≥0∞) ^ G.homogeneousDimension) ^ (1 / p) * ENNReal.ofReal (60 * C)) *
        (ENNReal.ofReal a * h₁ + ENNReal.ofReal b * h₂) := by
      simp only [e₁, e₂, hCa, hCb, mul_add, mul_assoc]

end HeatKernel

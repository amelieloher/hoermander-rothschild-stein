-- Copyright (c) 2026 Scott Armstrong and Amélie Loher. All rights reserved.
-- Released under Apache 2.0 license as described in the file LICENSE.
module

public import HeatKernel.Poincare.HomogeneousPacking
public import HeatKernel.Poincare.WhitneyPathBounds

/-! Uniform packing bounds for a single radius band of radial Whitney balls. -/

@[expose] public section
set_option autoImplicit false
set_option relaxedAutoImplicit false
noncomputable section
open Set Metric MeasureTheory
open scoped ENNReal

namespace HeatKernel

/-- Meeting balls in one dyadic radius band have a uniform homogeneous packing bound.
The center bound is explicit, so the lemma also applies to any family with that geometry. -/
theorem card_le_of_radial_ball_radius_band {E ι : Type*} [MetricSpace E]
    [MeasurableSpace E] [BorelSpace E] (μ : Measure E) (Q : ℕ) (v : ℝ≥0∞)
    (hv0 : v ≠ 0) (hvtop : v ≠ ⊤)
    (hvolume : ∀ x : E, ∀ r : ℝ, 0 < r → μ (ball x r) = ENNReal.ofReal (r ^ Q) * v)
    (s : Finset ι) (z : ι → E) (a : ι → ℝ) (x : E) {h κ : ℝ}
    (hh : 0 < h) (hκ : 0 ≤ κ + 10) (k : ℕ) (hk : 0 < k)
    (hscale : 2 * κ + 22 ≤ (k : ℝ))
    (hdisj : (s : Set ι).PairwiseDisjoint fun i => ball (z i) (a i))
    (hlower : ∀ i ∈ s, h ≤ a i) (hupper : ∀ i ∈ s, a i ≤ 2 * h)
    (hcenter : ∀ i ∈ s, dist x (z i) ≤ (κ + 10) * a i) : s.card ≤ k ^ Q := by
  apply card_le_of_homogeneous_ball_packing μ Q v hv0 hvtop hvolume s z a x hh k hk
    hdisj hlower
  intro i hi y hy
  apply mem_ball.mpr
  have hd := hcenter i hi
  have ha := hupper i hi
  have hm : (κ + 10) * a i ≤ (κ + 10) * (2 * h) :=
    mul_le_mul_of_nonneg_left ha hκ
  have hk' : (2 * κ + 22) * h ≤ (k : ℝ) * h :=
    mul_le_mul_of_nonneg_right hscale hh.le
  have ht := dist_triangle y (z i) x
  have hy' := mem_ball.mp hy
  rw [dist_comm (z i) x] at ht
  nlinarith

end HeatKernel

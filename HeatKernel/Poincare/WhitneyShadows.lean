-- Copyright (c) 2026 Scott Armstrong and Amélie Loher. All rights reserved.
-- Released under Apache 2.0 license as described in the file LICENSE.
module

public import HeatKernel.Poincare.WhitneyPathBounds
public import Mathlib.Topology.Algebra.InfiniteSum.ENNReal
public import Mathlib.MeasureTheory.Measure.Basic
public import Mathlib.MeasureTheory.Constructions.BorelSpace.Basic

/-! Shadow measure bounds from disjointness and radial center estimates. -/

@[expose] public section
set_option autoImplicit false
set_option relaxedAutoImplicit false
noncomputable section
open Set Metric MeasureTheory
open scoped ENNReal BigOperators

namespace HeatKernel

/-- Disjoint balls with the radial shadow radius and center bounds fit into one enlarged
ball, so their total measure is bounded by that enlarged ball's measure. -/
theorem sum_measure_le_of_radial_shadow {E ι : Type*} [MetricSpace E]
    [MeasurableSpace E] [BorelSpace E] (μ : Measure E) (s : Finset ι)
    (z : ι → E) (b : ι → ℝ) (w : E) {a κ : ℝ}
    (hdisj : (s : Set ι).PairwiseDisjoint fun i => ball (z i) (b i))
    (hradius : ∀ i ∈ s, b i ≤ 3 * a)
    (hcenter : ∀ i ∈ s, dist (z i) w ≤ (κ + 10) * a) :
    (∑ i ∈ s, μ (ball (z i) (b i))) ≤ μ (ball w ((κ + 13) * a)) := by
  rw [← measure_biUnion_finset hdisj (fun _ _ => isOpen_ball.measurableSet)]
  apply measure_mono
  exact iUnion₂_subset fun i hi =>
    ball_subset_of_radius_and_center_bound (hradius i hi) (hcenter i hi)

/-- Exact homogeneous volume turns the radial shadow containment into a bound by the
measure of the shadow's selected ball. -/
theorem sum_measure_le_homogeneous_radial_shadow {E ι : Type*} [MetricSpace E]
    [MeasurableSpace E] [BorelSpace E] (μ : Measure E) (Q : ℕ) (v : ℝ≥0∞)
    (hvolume : ∀ x : E, ∀ r : ℝ, 0 < r → μ (ball x r) = ENNReal.ofReal (r ^ Q) * v)
    (s : Finset ι) (z : ι → E) (b : ι → ℝ) (w : E) {a κ : ℝ}
    (ha : 0 < a) (hκ : 0 < κ + 13)
    (hdisj : (s : Set ι).PairwiseDisjoint fun i => ball (z i) (b i))
    (hradius : ∀ i ∈ s, b i ≤ 3 * a)
    (hcenter : ∀ i ∈ s, dist (z i) w ≤ (κ + 10) * a) :
    (∑ i ∈ s, μ (ball (z i) (b i))) ≤
      ENNReal.ofReal ((κ + 13) ^ Q) * μ (ball w a) := by
  calc
    (∑ i ∈ s, μ (ball (z i) (b i))) ≤ μ (ball w ((κ + 13) * a)) :=
      sum_measure_le_of_radial_shadow μ s z b w hdisj hradius hcenter
    _ = ENNReal.ofReal ((κ + 13) ^ Q) * μ (ball w a) := by
      rw [hvolume w ((κ + 13) * a) (mul_pos hκ ha), hvolume w a ha,
        mul_pow, ENNReal.ofReal_mul (pow_nonneg hκ.le Q), mul_assoc]

/-- The homogeneous shadow estimate also bounds the full nonnegative sum over an
arbitrary disjoint index family, by applying the finite estimate to every finite subset. -/
theorem tsum_measure_le_homogeneous_radial_shadow {E ι : Type*} [MetricSpace E]
    [MeasurableSpace E] [BorelSpace E] (μ : Measure E) (Q : ℕ) (v : ℝ≥0∞)
    (hvolume : ∀ x : E, ∀ r : ℝ, 0 < r → μ (ball x r) = ENNReal.ofReal (r ^ Q) * v)
    (z : ι → E) (b : ι → ℝ) (w : E) {a κ : ℝ}
    (ha : 0 < a) (hκ : 0 < κ + 13)
    (hdisj : Pairwise fun i j => Disjoint (ball (z i) (b i)) (ball (z j) (b j)))
    (hradius : ∀ i, b i ≤ 3 * a)
    (hcenter : ∀ i, dist (z i) w ≤ (κ + 10) * a) :
    (∑' i, μ (ball (z i) (b i))) ≤
      ENNReal.ofReal ((κ + 13) ^ Q) * μ (ball w a) := by
  apply ENNReal.summable.tsum_le_of_sum_le
  intro s
  exact sum_measure_le_homogeneous_radial_shadow μ Q v hvolume s z b w ha hκ
    (fun i _ j _ hij => hdisj hij) (fun i _ => hradius i) (fun i _ => hcenter i)

end HeatKernel

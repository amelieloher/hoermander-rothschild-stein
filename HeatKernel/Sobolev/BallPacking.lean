-- Copyright (c) 2026 Scott Armstrong and Amélie Loher. All rights reserved.
-- Released under Apache 2.0 license as described in the file LICENSE.
module

public import Mathlib.MeasureTheory.Measure.Basic
public import Mathlib.MeasureTheory.Constructions.BorelSpace.Metric
public import Mathlib.Topology.Algebra.InfiniteSum.ENNReal
import Mathlib.Tactic

/-! # Equal-volume packing and overlap estimates for ball families -/

@[expose] public section
open Set Metric MeasureTheory
open scoped ENNReal BigOperators
namespace HeatKernel.Sobolev

/-- A finite family of disjoint equal-volume balls is bounded by the containing-ball ratio. -/
theorem card_le_of_disjoint_equal_volume_balls {α ι : Type*}
    [PseudoMetricSpace α] [MeasurableSpace α] [BorelSpace α]
    {μ : Measure α} (c : ι → α) (I : Finset ι) {x : α} {r R : ℝ} {v K : ℝ≥0∞}
    (hv : v ≠ 0) (hvtop : v ≠ ⊤)
    (hdisjoint : (I : Set ι).PairwiseDisjoint (fun i => ball (c i) r))
    (hvolume : ∀ i ∈ I, μ (ball (c i) r) = v)
    (hcenters : ∀ i ∈ I, dist (c i) x < R)
    (houter : μ (ball x (R + r)) ≤ K * v) : (I.card : ℝ≥0∞) ≤ K := by
  have hsub : (⋃ i ∈ I, ball (c i) r) ⊆ ball x (R + r) := by
    apply iUnion₂_subset
    intro i hi y hy
    rw [mem_ball] at hy ⊢
    exact (dist_triangle y (c i) x).trans_lt (by linarith [hcenters i hi])
  have hsum : (I.card : ℝ≥0∞) * v ≤ K * v := by
    calc
      _ = ∑ i ∈ I, v := by simp [nsmul_eq_mul]
      _ = ∑ i ∈ I, μ (ball (c i) r) :=
        Finset.sum_congr rfl (fun i hi => (hvolume i hi).symm)
      _ = μ (⋃ i ∈ I, ball (c i) r) :=
        (measure_biUnion_finset hdisjoint (fun _ _ => measurableSet_ball)).symm
      _ ≤ μ (ball x (R + r)) := measure_mono hsub
      _ ≤ K * v := houter
  exact (ENNReal.mul_le_mul_iff_left hv hvtop).mp hsum

/-- A containing-ball volume ratio bounds the total overlap of an arbitrary ball family. -/
theorem tsum_indicator_ball_le_of_disjoint_equal_volume {α ι : Type*}
    [PseudoMetricSpace α] [MeasurableSpace α] [BorelSpace α]
    {μ : Measure α} (c : ι → α) {r R : ℝ} {v K : ℝ≥0∞}
    (hv : v ≠ 0) (hvtop : v ≠ ⊤)
    (hdisjoint : Pairwise (fun i j => Disjoint (ball (c i) r) (ball (c j) r)))
    (hvolume : ∀ i, μ (ball (c i) r) = v)
    (houter : ∀ x, μ (ball x (R + r)) ≤ K * v) (x : α) :
    (∑' i, (ball (c i) R).indicator (fun _ => (1 : ℝ≥0∞)) x) ≤ K := by
  classical
  apply ENNReal.summable.tsum_le_of_sum_le
  intro I
  let J := I.filter (fun i => x ∈ ball (c i) R)
  have hcard : (J.card : ℝ≥0∞) ≤ K :=
    card_le_of_disjoint_equal_volume_balls c J hv hvtop
      (fun i _ j _ hij => hdisjoint hij) (fun i _ => hvolume i)
      (fun i hi => by simpa only [J, Finset.mem_filter, mem_ball, dist_comm] using
        (Finset.mem_filter.mp hi).2) (houter x)
  convert hcard using 1
  simp only [J, Finset.card_eq_sum_ones, Nat.cast_sum, Finset.sum_filter]
  apply Finset.sum_congr rfl
  intro i _
  by_cases hi : x ∈ ball (c i) R <;> simp [hi]

end HeatKernel.Sobolev

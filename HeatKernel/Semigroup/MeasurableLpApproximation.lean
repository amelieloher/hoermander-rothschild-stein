-- Copyright (c) 2026 Scott Armstrong and Amélie Loher. All rights reserved.
-- Released under Apache 2.0 license as described in the file LICENSE.
module

public import Mathlib.MeasureTheory.Function.LpSpace.InfiniteSum
public import Mathlib.MeasureTheory.Constructions.Polish.Basic
public import Mathlib.Topology.MetricSpace.PiNat

/-! # Measurable geometric approximations in separable normed spaces -/

@[expose] public section
noncomputable section
open MeasureTheory TopologicalSpace Set Filter
open scoped Topology
namespace HeatKernel

theorem exists_measurable_geometric_approximation
    {α E : Type*} [MeasurableSpace α] [NormedAddCommGroup E]
    [MeasurableSpace E] [BorelSpace E] [SeparableSpace E]
    (T : α → E) (hT : Measurable T) :
    ∃ d : ℕ → E, ∃ k : ℕ → α → ℕ,
      (∀ n, Measurable (k n)) ∧
      ∀ n a, dist (T a) (d (k n a)) < (1 / 2 : ℝ) ^ n := by
  classical
  let d := denseSeq E
  have hex (n : ℕ) (a : α) : ∃ j, dist (T a) (d j) < (1 / 2 : ℝ) ^ n :=
    (denseRange_denseSeq E).exists_dist_lt (T a) (by positivity)
  let k : ℕ → α → ℕ := fun n a => Nat.find (hex n a)
  refine ⟨d, k, ?_, fun n a => Nat.find_spec (hex n a)⟩
  intro n
  exact measurable_find (hex n) (fun j =>
    measurableSet_lt (hT.dist measurable_const) measurable_const)

theorem summable_norm_geometric_approximation_differences
    {E : Type*} [NormedAddCommGroup E] (v : ℕ → E) (u : E)
    (hv : ∀ n, dist u (v n) < (1 / 2 : ℝ) ^ n) :
    Summable (fun n => ‖v (n + 1) - v n‖) := by
  have hs : Summable (fun n : ℕ => (2 : ℝ) * (1 / 2 : ℝ) ^ n) :=
    (summable_geometric_of_lt_one (by norm_num : (0 : ℝ) ≤ 1 / 2)
      (by norm_num : (1 / 2 : ℝ) < 1)).mul_left 2
  apply Summable.of_nonneg_of_le (fun n => norm_nonneg _) (fun n => ?_) hs
  rw [← dist_eq_norm]
  have hd := dist_triangle (v (n + 1)) u (v n)
  have h1 := hv (n + 1)
  have h2 := hv n
  rw [dist_comm (v (n + 1)) u] at hd
  rw [pow_succ] at h1
  nlinarith only [hd, h1, h2, pow_nonneg (by norm_num : (0 : ℝ) ≤ 1 / 2) n]

theorem hasSum_geometric_approximation_differences
    {E : Type*} [NormedAddCommGroup E] (v : ℕ → E) (u : E)
    (hv : ∀ n, dist u (v n) < (1 / 2 : ℝ) ^ n) :
    HasSum (fun n => v (n + 1) - v n) (u - v 0) := by
  have ht : Tendsto v atTop (𝓝 u) := by
    apply tendsto_iff_dist_tendsto_zero.mpr
    simp_rw [dist_comm _ u]
    apply squeeze_zero (fun n => dist_nonneg) (fun n => (hv n).le)
    exact tendsto_pow_atTop_nhds_zero_of_lt_one (by norm_num) (by norm_num)
  apply (hasSum_iff_tendsto_nat_of_summable_norm
    (summable_norm_geometric_approximation_differences v u hv)).mpr
  simpa only [Finset.sum_range_sub] using ht.sub_const (v 0)

end HeatKernel

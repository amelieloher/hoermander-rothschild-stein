-- Copyright (c) 2026 Scott Armstrong and Amélie Loher. All rights reserved.
-- Released under Apache 2.0 license as described in the file LICENSE.
module

public import RothschildStein.G4.SmallControlTaylorBounds
public import Mathlib.Topology.MetricSpace.Basic

@[expose] public section
set_option autoImplicit false
set_option relaxedAutoImplicit false
noncomputable section
open Set Metric Filter
open scoped BigOperators Topology

namespace RothschildStein.G4

/-- A finite Taylor-error polynomial and a positive-order remainder
can be made smaller than one half with a numerical radius e≤min(1,t).
The zero-order Taylor case is included. -/
theorem exists_weightedTaylor_smallness (m d : ℕ) (hd : 0 < d)
    (c : ℕ → ℝ) (A t Δ : ℝ) (ht : 0 < t) (_hΔ : 0 < Δ) :
    ∃ e : ℝ, 0 < e ∧ e ≤ 1 ∧ e ≤ t ∧
      (∑ j ∈ Finset.range m, c (j + 1) * e ^ (j + 1)) +
        A * e ^ d / (t * Δ) < 1 / 2 := by
  classical
  let P : ℝ → ℝ := fun e =>
    (∑ j ∈ Finset.range m, c (j + 1) * e ^ (j + 1)) +
      A * e ^ d / (t * Δ)
  have hP : Continuous P := by
    apply Continuous.add
    · apply continuous_finsetSum
      intro j hj
      exact continuous_const.mul (continuous_id.pow (j + 1))
    · exact (continuous_const.mul (continuous_id.pow d)).div_const _
  have hP0 : P 0 = 0 := by
    dsimp [P]
    simp [hd.ne']
  have hn : {e : ℝ | P e < 1 / 2} ∈ 𝓝 0 :=
    hP.continuousAt.preimage_mem_nhds (isOpen_Iio.mem_nhds (by rw [hP0]; norm_num))
  obtain ⟨δ, hδ, hball⟩ := Metric.mem_nhds_iff.mp hn
  let e := min (min δ t) 1 / 2
  have hmin : 0 < min (min δ t) 1 := lt_min (lt_min hδ ht) zero_lt_one
  have he : 0 < e := half_pos hmin
  have heδ : e < δ := (half_lt_self hmin).trans_le ((min_le_left _ _).trans (min_le_left _ _))
  have het : e ≤ t := (half_lt_self hmin).le.trans ((min_le_left _ _).trans (min_le_right _ _))
  have he1 : e ≤ 1 := (half_lt_self hmin).le.trans (min_le_right _ _)
  refine ⟨e, he, he1, het, ?_⟩
  exact hball (by simpa only [mem_ball, dist_zero_right, Real.norm_eq_abs, abs_of_pos he] using heδ)

end RothschildStein.G4

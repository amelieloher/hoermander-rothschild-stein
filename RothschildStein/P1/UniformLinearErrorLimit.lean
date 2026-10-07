-- Copyright (c) 2026 Scott Armstrong and Amélie Loher. All rights reserved.
-- Released under Apache 2.0 license as described in the file LICENSE.
module

public import Mathlib.Topology.MetricSpace.Pseudo.Basic
public import Mathlib.Analysis.Normed.Field.Basic
public import Mathlib.Topology.Instances.Real.Lemmas

set_option autoImplicit false
set_option relaxedAutoImplicit false
@[expose] public section
open Set Filter
open scoped Topology
namespace RothschildStein.P1

/-- A uniform linear error estimate at positive
radii gives uniform convergence, without any bound on the ambient set. -/
theorem tendstoUniformlyOn_of_linearError {E : Type*} {K : Set E}
    {F : ℝ → E → ℝ} {f : E → ℝ} {r A : ℝ} (hr : 0 < r)
    (hb : ∀ ξ ∈ K, ∀ ε : ℝ, 0 < ε → ε ≤ r → ‖F ε ξ - f ξ‖ ≤ A * ε) :
    TendstoUniformlyOn F f (𝓝[>] (0 : ℝ)) K := by
  have ht : Tendsto (fun ε : ℝ => A * ε) (𝓝[>] (0 : ℝ)) (𝓝 0) := by
    simpa only [mul_zero, id_eq] using
      (tendsto_id.mono_left nhdsWithin_le_nhds :
        Tendsto (fun ε : ℝ => ε) (𝓝[>] (0 : ℝ)) (𝓝 0)).const_mul A
  apply Metric.tendstoUniformlyOn_iff.mpr
  intro δ hδ
  filter_upwards [self_mem_nhdsWithin,
    mem_nhdsWithin_of_mem_nhds (Iio_mem_nhds hr), ht.eventually (Iio_mem_nhds hδ)]
    with ε hε hεr hεδ
  intro ξ hξ
  rw [dist_comm, dist_eq_norm]
  exact (hb ξ hξ ε hε hεr.le).trans_lt hεδ

end RothschildStein.P1

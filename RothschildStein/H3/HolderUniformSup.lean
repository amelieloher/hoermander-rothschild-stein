-- Copyright (c) 2026 Scott Armstrong and Amélie Loher. All rights reserved.
-- Released under Apache 2.0 license as described in the file LICENSE.
module

public import RothschildStein.H2.HolderSpaces
public import Mathlib.Topology.UniformSpace.UniformConvergence

set_option autoImplicit false
set_option relaxedAutoImplicit false
@[expose] public section
noncomputable section
open Set Filter
open scoped ENNReal Topology
namespace RothschildStein.H3
variable {X T : Type*}

/-- (iv) Uniform convergence controls the exact global
supremum of the error; BB Theorem 8.52, pp. 381–382. -/
theorem tendsto_holderSup_sub_zero_of_uniform
    (l : Filter T) (F : T → X → ℝ) (f : X → ℝ)
    (h : TendstoUniformly F f l) :
    Tendsto (fun t => H2.holderSup univ (fun x => F t x - f x)) l (𝓝 0) := by
  apply ENNReal.tendsto_nhds_zero.mpr
  intro ε hε
  by_cases he : ε = ⊤
  · simp only [he, le_top, eventually_true]
  · have hp : 0 < ε.toReal := ENNReal.toReal_pos hε.ne' he
    filter_upwards [Metric.tendstoUniformly_iff.mp h ε.toReal hp] with t ht
    have hb := H2.holderSup_le_of_bound (A := (univ : Set X))
      (fun x _ => (show |F t x - f x| < ε.toReal by
        simpa only [Real.dist_eq, abs_sub_comm] using ht x).le)
    exact hb.trans_eq (ENNReal.ofReal_toReal he)

end RothschildStein.H3

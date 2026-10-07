-- Copyright (c) 2026 Scott Armstrong and Amélie Loher. All rights reserved.
-- Released under Apache 2.0 license as described in the file LICENSE.
module

public import RothschildStein.P1.UniformRadialRows

set_option autoImplicit false
set_option relaxedAutoImplicit false
set_option backward.isDefEq.respectTransparency false
@[expose] public section
open Set Filter
open scoped Topology BigOperators
namespace RothschildStein.P1

/-- Finite sums of actual compact-uniform
limits retain uniform convergence on the same center set. -/
theorem tendstoUniformlyOn_finsetSum {E A : Type*} (s : Finset A)
    {K : Set E} (F : A → ℝ → E → ℝ) (f : A → E → ℝ)
    (ht : ∀ a ∈ s, TendstoUniformlyOn (F a) (f a) (𝓝[>] (0 : ℝ)) K) :
    TendstoUniformlyOn (fun ε x => ∑ a ∈ s, F a ε x)
      (fun x => ∑ a ∈ s, f a x) (𝓝[>] (0 : ℝ)) K := by
  classical
  induction s using Finset.induction_on with
  | empty =>
    simp only [Finset.sum_empty]
    exact (tendsto_const_nhds : Tendsto (fun _ : ℝ => (0 : ℝ))
      (𝓝[>] (0 : ℝ)) (𝓝 0)).tendstoUniformlyOn_const K
  | @insert a s ha ih =>
    have hA := ht a (Finset.mem_insert_self a s)
    have hS := ih (fun b hb => ht b (Finset.mem_insert_of_mem hb))
    simpa only [Finset.sum_insert ha, Pi.add_def] using hA.add hS

end RothschildStein.P1

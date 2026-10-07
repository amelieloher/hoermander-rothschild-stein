-- Copyright (c) 2026 Scott Armstrong and Amélie Loher. All rights reserved.
-- Released under Apache 2.0 license as described in the file LICENSE.
module

public import Mathlib.Topology.Algebra.IsUniformGroup.Basic
public import RothschildStein.S.HolderUniformConvergence

set_option autoImplicit false
set_option relaxedAutoImplicit false
set_option backward.isDefEq.respectTransparency false
@[expose] public section
open Set Filter
namespace RothschildStein.S
variable {A E ι : Type*}

/-- Finite lists of uniformly vanishing real error terms
have uniformly vanishing sums (BB Thm 2.20, p. 86; finite assembly). -/
theorem tendstoUniformlyOn_listSum_zero
    (items : List A) (F : A → ι → E → ℝ) {l : Filter ι} {U : Set E}
    (h : ∀ a ∈ items,TendstoUniformlyOn (F a) (fun _ => 0) l U) :
    TendstoUniformlyOn (fun j x => (items.map (fun a => F a j x)).sum) (fun _ => 0) l U := by
  induction items with
  | nil =>
    apply Metric.tendstoUniformlyOn_iff.mpr
    intro ε he
    exact Eventually.of_forall (fun _ x _ => by simpa only [List.map_nil,List.sum_nil,dist_self] using he)
  | cons a items ih =>
    have hh := h a List.mem_cons_self
    have ht := ih (fun b hb => h b (List.mem_cons_of_mem a hb))
    apply Metric.tendstoUniformlyOn_iff.mpr
    intro ε he
    filter_upwards [Metric.tendstoUniformlyOn_iff.mp hh (ε/2) (half_pos he),
      Metric.tendstoUniformlyOn_iff.mp ht (ε/2) (half_pos he)] with j hj hk
    intro x hx
    have ha : ‖F a j x‖ < ε/2 := by simpa only [dist_zero_left] using hj x hx
    have hb : ‖(items.map (fun b => F b j x)).sum‖ < ε/2 := by
      simpa only [dist_zero_left] using hk x hx
    simp only [List.map_cons,List.sum_cons,dist_zero_left]
    exact (norm_add_le _ _).trans_lt (by linarith)

end RothschildStein.S

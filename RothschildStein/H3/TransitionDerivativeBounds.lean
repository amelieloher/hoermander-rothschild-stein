-- Copyright (c) 2026 Scott Armstrong and Amélie Loher. All rights reserved.
-- Released under Apache 2.0 license as described in the file LICENSE.
module

public import RothschildStein.H3.QuasiballProfile
public import Mathlib.Analysis.Calculus.IteratedDeriv.Lemmas
public import Mathlib.Analysis.Normed.Group.Bounded
public import Mathlib.Topology.Algebra.Support

set_option autoImplicit false
set_option relaxedAutoImplicit false
@[expose] public section
noncomputable section
namespace RothschildStein.H3
open Set Filter
open scoped Topology

/-- Positive-order derivatives of the fixed transition vanish
outside the closed unit interval, by locality of iterated derivatives. -/
theorem transition_iteratedDeriv_zero_outside {j : ℕ} (hj : 0 < j)
    {x : ℝ} (hx : x < 0 ∨ 1 < x) : iteratedDeriv j Real.smoothTransition x = 0 := by
  rcases hx with hx | hx
  · have he : Real.smoothTransition =ᶠ[𝓝 x] (fun _ => (0 : ℝ)) := by
      filter_upwards [eventually_lt_nhds hx] with y hy
      exact Real.smoothTransition.zero_of_nonpos hy.le
    have hd := (he.iteratedDeriv j).self_of_nhds
    simpa only [iteratedDeriv_const, ite_eq_right hj.ne'] using hd
  · have he : Real.smoothTransition =ᶠ[𝓝 x] (fun _ => (1 : ℝ)) := by
      filter_upwards [eventually_gt_nhds hx] with y hy
      exact Real.smoothTransition.one_of_one_le hy.le
    have hd := (he.iteratedDeriv j).self_of_nhds
    simpa only [iteratedDeriv_const, ite_eq_right hj.ne'] using hd

/-- Every positive-order transition derivative is compactly
supported in the same fixed interval. -/
theorem transition_iteratedDeriv_compact {j : ℕ} (hj : 0 < j) :
    HasCompactSupport (iteratedDeriv j Real.smoothTransition) := by
  change IsCompact (tsupport (iteratedDeriv j Real.smoothTransition))
  apply (isCompact_Icc : IsCompact (Icc (0 : ℝ) 1)).of_isClosed_subset (isClosed_tsupport _) ?_
  change closure (Function.support (iteratedDeriv j Real.smoothTransition)) ⊆ Icc 0 1
  apply closure_minimal ?_ isClosed_Icc
  intro x hx
  by_contra hnot
  have hout : x < 0 ∨ 1 < x := by
    simpa only [mem_Icc, not_and_or, not_le] using hnot
  exact hx (transition_iteratedDeriv_zero_outside hj hout)

/-- The profile derivative constants are finite and independent of
centers and radii (BB Lemma 8.40, p. 370); compact support gives the bound. -/
theorem exists_transition_derivative_bound {j : ℕ} (hj : 0 < j) :
    ∃ κ : ℝ, 0 ≤ κ ∧ ∀ x, |iteratedDeriv j Real.smoothTransition x| ≤ κ := by
  have hc : Continuous (iteratedDeriv j Real.smoothTransition) :=
    (Real.smoothTransition.contDiff (n := (⊤ : ℕ∞))).continuous_iteratedDeriv j (by simp)
  obtain ⟨κ, hκ⟩ := hc.bounded_above_of_compact_support (transition_iteratedDeriv_compact hj)
  refine ⟨max κ 0, le_max_right _ _, ?_⟩
  intro x
  have hxκ : |iteratedDeriv j Real.smoothTransition x| ≤ κ := by
    simpa only [Real.norm_eq_abs] using hκ x
  exact hxκ.trans (le_max_left κ 0)

end RothschildStein.H3

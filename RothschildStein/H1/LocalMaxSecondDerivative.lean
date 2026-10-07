-- Copyright (c) 2026 Scott Armstrong and Amélie Loher. All rights reserved.
-- Released under Apache 2.0 license as described in the file LICENSE.
module

public import Mathlib.Analysis.Calculus.DerivativeTest
public import Mathlib.Analysis.Calculus.ContDiff.Basic
public import Mathlib.Analysis.Calculus.ContDiff.Operations
public import Mathlib.Analysis.Calculus.ContDiff.Comp
public import Mathlib.Analysis.Calculus.LocalExtr.Basic

set_option autoImplicit false
set_option relaxedAutoImplicit false
@[expose] public section
noncomputable section
open Filter
open scoped Topology
namespace RothschildStein.H1

/-- Lemma 4.1, scalar second-order necessary condition.
A positive second derivative would produce a local minimum as well as
a local maximum, hence a locally constant function and zero second derivative
(BB Thm 1.57, pp. 37–38). -/
theorem IsLocalMax.second_deriv_nonpos {f : ℝ → ℝ} {x : ℝ}
    (h : IsLocalMax f x) (hc : ContinuousAt f x) : deriv (deriv f) x ≤ 0 := by
  by_contra hn
  have hp : 0 < deriv (deriv f) x := lt_of_not_ge hn
  have hmin := isLocalMin_of_deriv_deriv_pos hp h.deriv_eq_zero hc
  have he : f =ᶠ[𝓝 x] fun _ => f x := by
    filter_upwards [h, hmin] with y hy hy'
    exact le_antisymm hy hy'
  have he' : deriv f =ᶠ[𝓝 x] fun _ => (0 : ℝ) := by
    filter_upwards [he.deriv] with y hy
    simpa only [deriv_const] using hy
  have hz : deriv (deriv f) x = 0 := by
    simpa only [deriv_const] using he'.deriv_eq
  exact (ne_of_gt hp) hz

end RothschildStein.H1

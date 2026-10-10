-- Copyright (c) 2026 Scott Armstrong and Amélie Loher. All rights reserved.
-- Released under Apache 2.0 license as described in the file LICENSE.
module

public import HeatKernel.Moser.PowerRangeExtensions
import Mathlib.Tactic

/-! # Lower-truncated real powers with exponents at most one -/

@[expose] public section
set_option autoImplicit false
set_option relaxedAutoImplicit false
noncomputable section
open Set Filter
open scoped Topology NNReal
namespace HeatKernel.Sobolev

/-- A real power held constant below a positive threshold. -/
def lowerTruncatedRpow (c p s : ℝ) : ℝ := (max c s)^p

/-- Powers of exponent at most one have a globally Lipschitz lower truncation. -/
theorem lipschitzWith_lowerTruncatedRpow {c p : ℝ} (hc : 0 < c) (hp : p ≤ 1) :
    LipschitzWith (Real.toNNReal (|p| * c^(p-1))) (lowerTruncatedRpow c p) :=
  lipschitzWith_clipped_derivative (lipschitzOnWith_rpow_Ici hc hp)

/-- Away from the threshold, a lower-truncated real power is C¹. -/
theorem contDiffAt_lowerTruncatedRpow {c p s : ℝ} (hc : 0 < c) (hs : s ≠ c) :
    ContDiffAt ℝ 1 (lowerTruncatedRpow c p) s := by
  rcases lt_or_gt_of_ne hs with hsc | hcs
  · apply (contDiffAt_const (c := c^p)).congr_of_eventuallyEq
    filter_upwards [Iio_mem_nhds hsc] with t ht
    simp only [lowerTruncatedRpow, max_eq_left ht.le]
  · apply (Real.contDiffAt_rpow_const_of_ne (p := p) (hc.trans hcs).ne').congr_of_eventuallyEq
    filter_upwards [Ioi_mem_nhds hcs] with t ht
    simp only [lowerTruncatedRpow, max_eq_right ht.le]

end HeatKernel.Sobolev

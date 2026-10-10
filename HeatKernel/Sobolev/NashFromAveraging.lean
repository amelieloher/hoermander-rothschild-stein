-- Copyright (c) 2026 Scott Armstrong and Amélie Loher. All rights reserved.
-- Released under Apache 2.0 license as described in the file LICENSE.
module

public import HeatKernel.Sobolev.NashOptimization
public import Mathlib.Analysis.Normed.Group.Basic
import Mathlib.Tactic

/-!
# Nash estimates from local averaging operators

The averaging parameter is the radius divided by the radius of the ambient
ball. The two analytic inputs are the Poincaré averaging error and the volume
bound on the average. The inhomogeneous energy controls both the gradient term
and the quadratic norm, allowing all averaging radii in the optimization.
-/

@[expose] public section

namespace HeatKernel.Sobolev

/-- A local radius bound extends to every radius after including the quadratic norm. -/
theorem radius_approximation_of_unit_radius_bound {L C G W ν : ℝ}
    (hL : 0 ≤ L) (hC : 1 ≤ C) (hG : 0 ≤ G) (hW : 0 ≤ W)
    (hsmall : ∀ s : ℝ, 0 < s → s ≤ 1 →
      L ≤ C * s * G + W * s ^ (-ν / 2)) :
    ∀ s : ℝ, 0 < s → L ≤ C * s * (G + L) + W * s ^ (-ν / 2) := by
  intro s hs
  have hC₀ : 0 ≤ C := by linarith
  have htail : 0 ≤ W * s ^ (-ν / 2) := mul_nonneg hW (Real.rpow_nonneg hs.le _)
  by_cases hs₁ : s ≤ 1
  · have h := hsmall s hs hs₁
    nlinarith [mul_nonneg (mul_nonneg hC₀ hs.le) hL]
  · have hs₁ : 1 ≤ s := le_of_not_ge hs₁
    have hCs : 1 ≤ C * s := by nlinarith
    nlinarith [mul_nonneg (sub_nonneg.mpr hCs) hL,
      mul_nonneg (mul_nonneg hC₀ hs.le) hG]

/-- Local averaging bounds imply Nash, including the zero first-moment case. -/
theorem sq_le_nash_of_unit_radius_bound {L C G W E ν : ℝ}
    (hL : 0 ≤ L) (hC : 1 ≤ C) (hG : 0 ≤ G) (hW : 0 ≤ W)
    (hν : 0 < ν) (henergy : G ^ 2 + L ^ 2 ≤ E) (hzero : W = 0 → L = 0)
    (hsmall : ∀ s : ℝ, 0 < s → s ≤ 1 →
      L ≤ C * s * G + W * s ^ (-ν / 2)) :
    L ^ 2 ≤ ((C + 1) ^ 2 * 2 ^ (ν / (ν + 2))) *
      E ^ (ν / (ν + 2)) * W ^ (4 / (ν + 2)) := by
  have hE : 0 ≤ E := (add_nonneg (sq_nonneg G) (sq_nonneg L)).trans henergy
  by_cases hL₀ : L = 0
  · rw [hL₀, zero_pow (by norm_num : (2 : ℕ) ≠ 0)]
    positivity
  have hLpos : 0 < L := lt_of_le_of_ne hL (Ne.symm hL₀)
  have hWpos : 0 < W := lt_of_le_of_ne hW (Ne.symm (fun hw => hL₀ (hzero hw)))
  have hU : 0 < G + L := by linarith
  have hU₂ : (G + L) ^ 2 ≤ 2 * E := by nlinarith [sq_nonneg (G - L)]
  have h := sq_le_nash_of_radius_approximation hL hU hWpos hν hU₂
    (radius_approximation_of_unit_radius_bound hL hC hG hW hsmall)
  rw [Real.mul_rpow (by norm_num : (0 : ℝ) ≤ 2) hE] at h
  convert h using 1
  ring

end HeatKernel.Sobolev

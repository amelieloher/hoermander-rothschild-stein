-- Copyright (c) 2026 Scott Armstrong and Amélie Loher. All rights reserved.
-- Released under Apache 2.0 license as described in the file LICENSE.
module

public import Mathlib.Analysis.Calculus.MeanValue
public import Mathlib.Analysis.Calculus.Deriv.Slope

/-! # Bounds for scalar difference quotients

A uniform derivative bound controls every nontrivial difference quotient,
and hence its error relative to the derivative at the base point.
-/

@[expose] public section

open Set

namespace HeatKernel

/-- A bounded scalar derivative bounds the error of each nontrivial difference quotient. -/
theorem norm_slope_error_le_of_derivative_bound (f d : ℝ → ℝ) {C a t : ℝ}
    (hderiv : ∀ s, HasDerivAt f (d s) s) (hb : ∀ s, ‖d s‖ ≤ C) (ht : t ≠ a) :
    ‖(t - a)⁻¹ * (f t - f a) - d a‖ ≤ 2 * C := by
  have hdiff : ‖f t - f a‖ ≤ C * ‖t - a‖ :=
    convex_univ.norm_image_sub_le_of_norm_hasDerivWithin_le
      (fun s _ => (hderiv s).hasDerivWithinAt) (fun s _ => hb s) (mem_univ a) (mem_univ t)
  have hne : ‖t - a‖ ≠ 0 := norm_ne_zero_iff.mpr (sub_ne_zero.mpr ht)
  have hquot : ‖(t - a)⁻¹ * (f t - f a)‖ ≤ C := by
    rw [norm_mul, norm_inv]
    calc
      ‖t - a‖⁻¹ * ‖f t - f a‖ ≤ ‖t - a‖⁻¹ * (C * ‖t - a‖) :=
        mul_le_mul_of_nonneg_left hdiff (inv_nonneg.mpr (norm_nonneg _))
      _ = C := by rw [mul_left_comm, inv_mul_cancel₀ hne, mul_one]
  exact (norm_sub_le _ _).trans (by linarith [hb a])

end HeatKernel

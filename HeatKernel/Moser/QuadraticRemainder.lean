-- Copyright (c) 2026 Scott Armstrong and Amélie Loher. All rights reserved.
-- Released under Apache 2.0 license as described in the file LICENSE.
module

public import Mathlib

/-! # Quadratic remainder bounds for nonlinear energy functionals

A Lipschitz scalar derivative gives a quadratic Taylor remainder. A continuous linear
candidate derivative with such a remainder is a Fréchet derivative on any normed space.
-/

@[expose] public section

open Set Filter Asymptotics
open scoped Topology NNReal

namespace HeatKernel

/-- A Lipschitz derivative gives a quadratic remainder, with a convenient nonsharp constant. -/
theorem norm_scalar_remainder_le_of_lipschitz_deriv {Φ : ℝ → ℝ} {L : ℝ≥0}
    (hΦ : Differentiable ℝ Φ) (hL : LipschitzWith L (deriv Φ)) (s k : ℝ) :
    ‖Φ (s + k) - Φ s - deriv Φ s * k‖ ≤ (L : ℝ) * ‖k‖ ^ 2 := by
  let R : ℝ → ℝ := fun t => Φ t - Φ s - deriv Φ s * (t - s)
  have hd : ∀ t, HasDerivAt R (deriv Φ t - deriv Φ s) t := by
    intro t
    simpa only [R, mul_one, Pi.sub_def, id_eq] using
      ((hΦ t).hasDerivAt.sub_const (Φ s)).sub
        (((hasDerivAt_id t).sub_const s).const_mul (deriv Φ s))
  have hb : ∀ t ∈ uIcc s (s + k), ‖deriv Φ t - deriv Φ s‖ ≤ (L : ℝ) * ‖k‖ := by
    intro t ht
    refine (hL.norm_sub_le t s).trans (mul_le_mul_of_nonneg_left ?_ L.coe_nonneg)
    simpa only [Real.norm_eq_abs, add_sub_cancel_left] using abs_sub_left_of_mem_uIcc ht
  have H := Convex.norm_image_sub_le_of_norm_hasDerivWithin_le
    (fun t _ => (hd t).hasDerivWithinAt) hb (convex_uIcc s (s + k))
    (left_mem_uIcc) (right_mem_uIcc)
  simpa only [R, sub_self, mul_zero, sub_zero, add_sub_cancel_left, pow_two, mul_assoc] using H

/-- A quadratic remainder bound proves Fréchet differentiability at a point. -/
theorem hasFDerivAt_of_quadratic_remainder {E F : Type*}
    [NormedAddCommGroup E] [NormedSpace ℝ E] [NormedAddCommGroup F] [NormedSpace ℝ F]
    {Φ : E → F} {v : E} (A : E →L[ℝ] F) {C : ℝ}
    (hbound : ∀ k, ‖Φ (v + k) - Φ v - A k‖ ≤ C * ‖k‖ ^ 2) :
    HasFDerivAt Φ A v := by
  apply hasFDerivAt_iff_isLittleO_nhds_zero.mpr
  have hb : (fun k => Φ (v + k) - Φ v - A k) =O[𝓝 0] (fun k : E => ‖k‖ ^ 2) :=
    isBigO_iff.mpr ⟨C, Eventually.of_forall fun k => by
      simpa only [Real.norm_of_nonneg (sq_nonneg _)] using hbound k⟩
  exact hb.trans_isLittleO (isLittleO_norm_pow_id (by norm_num : 1 < (2 : ℕ)))

end HeatKernel

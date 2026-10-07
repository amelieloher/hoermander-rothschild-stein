-- Copyright (c) 2026 Scott Armstrong and Amélie Loher. All rights reserved.
-- Released under Apache 2.0 license as described in the file LICENSE.
module

public import RothschildStein.S.FriedrichsInteriorPatch

set_option autoImplicit false
set_option relaxedAutoImplicit false
@[expose] public section
noncomputable section
open Set Metric
namespace RothschildStein.S
variable {n : ℕ}

/-- Interior mollifier samples remain in the fixed compact
coefficient tube (BB Thm 2.20, p. 86; buffer). -/
theorem add_smul_mem_interior_cthickening
    {U : Set (Fin n → ℝ)} {δ ε : ℝ} (hε : ε ∈ Ioo 0 δ)
    {x y : Fin n → ℝ} (hx : x ∈ U) (hy : y ∈ closedBall (0 : Fin n → ℝ) 1) :
    x+ε • y ∈ cthickening δ (closure U) := by
  apply mem_cthickening_of_dist_le (x+ε • y) x δ (closure U) (subset_closure hx)
  rw [dist_eq_norm,add_sub_cancel_left,norm_smul,Real.norm_of_nonneg hε.1.le]
  have hn : ‖y‖ ≤ 1 := by simpa only [mem_closedBall,dist_zero_right] using hy
  exact (mul_le_of_le_one_right hε.1.le hn).trans hε.2.le

/-- The original patch lies in any positive interior tube
(BB Thm 2.20, p. 86; buffer). -/
theorem subset_interior_cthickening {U : Set (Fin n → ℝ)} {δ : ℝ} (hd : 0 < δ) :
    U ⊆ cthickening δ (closure U) := by
  intro x hx
  apply mem_cthickening_of_dist_le x x δ (closure U) (subset_closure hx)
  simpa only [dist_self] using hd.le

end RothschildStein.S

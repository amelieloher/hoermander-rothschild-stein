-- Copyright (c) 2026 Scott Armstrong and Amélie Loher. All rights reserved.
-- Released under Apache 2.0 license as described in the file LICENSE.
module

public import RothschildStein.S.FriedrichsInteriorPatch

set_option autoImplicit false
set_option relaxedAutoImplicit false
set_option backward.isDefEq.respectTransparency false
@[expose] public section
noncomputable section
open Set MeasureTheory Function Metric TopologicalSpace
namespace RothschildStein.S
variable {n : ℕ}

/-- Interior kernels sample only Ω, so applying them to a local
representative equals applying them to its zero extension, pointwise
on the interior patch (BB Lemma 2.11, p. 74; domain). -/
theorem smoothFriedrichsKernelOp_eq_zeroExtension
    (Ω : Opens (Fin n → ℝ)) (K : SmoothFriedrichsKernel n)
    (h : (Fin n → ℝ) → ℝ) {ε : ℝ} (hε : 0 < ε)
    (x : Fin n → ℝ) (hx : closedBall x ε ⊆ Ω) :
    friedrichsKernelOp K.family h ε x =
      friedrichsKernelOp K.family ((Ω : Set (Fin n → ℝ)).indicator h) ε x := by
  unfold friedrichsKernelOp
  apply integral_congr_ae
  apply Filter.Eventually.of_forall
  intro y
  change K.family ε x y * h (x+ε • y) =
    K.family ε x y * (Ω : Set (Fin n → ℝ)).indicator h (x+ε • y)
  by_cases hy : ‖y‖ ≤ 1
  · have hz : x+ε • y ∈ (Ω : Set (Fin n → ℝ)) := by
      apply hx
      change dist (x+ε • y) x ≤ ε
      rw [dist_eq_norm,add_sub_cancel_left,norm_smul,Real.norm_of_nonneg hε.le]
      exact mul_le_of_le_one_right hε.le hy
    rw [indicator_of_mem hz]
  · rw [show K.family ε x y = 0 from K.vanish ((x,y),ε) (lt_of_not_ge hy)]
    simp only [zero_mul]

end RothschildStein.S

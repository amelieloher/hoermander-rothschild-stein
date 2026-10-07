-- Copyright (c) 2026 Scott Armstrong and Amélie Loher. All rights reserved.
-- Released under Apache 2.0 license as described in the file LICENSE.
module

public import RothschildStein.S.BaseKernelAllDimensions
public import RothschildStein.S.InteriorTubeTranslations
public import RothschildStein.S.WordDerivativeGerms

set_option autoImplicit false
set_option relaxedAutoImplicit false
set_option backward.isDefEq.respectTransparency false
@[expose] public section
noncomputable section
open Set MeasureTheory Function Filter Metric
open scoped Topology
namespace RothschildStein.S
variable {n q : ℕ}

/-- Mollifiers of functions agreeing on the fixed interior
tube agree on the patch at every smaller positive scale
(BB Thm 2.20, p. 86; exact cutoff identity). -/
theorem euclideanRegularize_eqOn_of_eqOn_interior_tube
    {U : Set (Fin n → ℝ)} {δ ε : ℝ} (hε : ε ∈ Ioo 0 δ)
    (f g : (Fin n → ℝ) → ℝ)
    (he : EqOn f g (cthickening δ (closure U))) :
    EqOn (euclideanRegularize n f ε) (euclideanRegularize n g ε) U := by
  intro x hx
  rw [← smoothBaseFriedrichsKernel_op f hε.1,← smoothBaseFriedrichsKernel_op g hε.1]
  unfold friedrichsKernelOp
  apply integral_congr_ae
  apply Eventually.of_forall
  intro y
  change (smoothBaseFriedrichsKernel n).family ε x y*f (x+ε • y) =
    (smoothBaseFriedrichsKernel n).family ε x y*g (x+ε • y)
  by_cases hy : y ∈ closedBall (0 : Fin n → ℝ) 1
  · rw [he (add_smul_mem_interior_cthickening hε hx hy)]
  · have hn : ¬ ‖y‖ ≤ 1 := by simpa only [mem_closedBall,dist_zero_right] using hy
    have hz : (smoothBaseFriedrichsKernel n).family ε x y = 0 :=
      (smoothBaseFriedrichsKernel n).vanish ((x,y),ε) (lt_of_not_ge hn)
    rw [hz]
    simp only [zero_mul]

/-- The cutoff replacement preserves every classical word
of mollification on the open patch (BB Theorem 2.20, p. 86). -/
theorem wordDerivative_regularize_eqOn_of_eqOn_interior_tube
    (X : Fin q → (Fin n → ℝ) → (Fin n → ℝ)) (I : List (Fin q))
    {U : Set (Fin n → ℝ)} (hU : IsOpen U) {δ ε : ℝ} (hε : ε ∈ Ioo 0 δ)
    (f g : (Fin n → ℝ) → ℝ)
    (he : EqOn f g (cthickening δ (closure U))) :
    EqOn (wordDerivative X I (euclideanRegularize n f ε))
      (wordDerivative X I (euclideanRegularize n g ε)) U := by
  intro x hx
  have hr : euclideanRegularize n f ε =ᶠ[𝓝 x] euclideanRegularize n g ε := by
    filter_upwards [hU.mem_nhds hx] with z hz
    exact euclideanRegularize_eqOn_of_eqOn_interior_tube hε f g he hz
  exact (wordDerivative_eventuallyEq X I hr).eq_of_nhds

end RothschildStein.S

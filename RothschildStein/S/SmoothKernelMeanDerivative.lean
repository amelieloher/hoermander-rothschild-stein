-- Copyright (c) 2026 Scott Armstrong and Amélie Loher. All rights reserved.
-- Released under Apache 2.0 license as described in the file LICENSE.
module

public import RothschildStein.S.CompactKernelDerivative
public import RothschildStein.S.ProductSectionDerivative
public import RothschildStein.S.SmoothFriedrichsKernels

set_option autoImplicit false
set_option relaxedAutoImplicit false
@[expose] public section
noncomputable section
open Set MeasureTheory Function Metric
open scoped Topology ContDiff
namespace RothschildStein.S
variable {n : ℕ}

/-- The x-derivative of a joint smooth kernel mean is the
integral of the x-derivative, with an actual common compact y-support
(BB pp. 76,78; zero-mean closure). -/
theorem fderiv_smoothKernelMean_apply (K : SmoothFriedrichsKernel n)
    (ε : ℝ) (x v : Fin n → ℝ) :
    fderiv ℝ (fun x => ∫ y, K.family ε x y) x v =
      ∫ y, fderiv ℝ K.toFun ((x,y),ε) ((v,0),0) := by
  have hk : ContDiff ℝ (⊤ : ℕ∞) (uncurry (K.family ε)) :=
    K.smooth.comp (contDiff_id.prodMk contDiff_const)
  have hs : ∀ x y, y ∉ closedBall (0 : Fin n → ℝ) 1 → K.family ε x y = 0 := by
    intro x y hy
    apply K.vanish ((x,y),ε)
    simpa only [mem_closedBall,dist_zero_right,not_le] using hy
  have H := fderiv_compactKernelIntegral_apply (isCompact_closedBall (0 : Fin n → ℝ) 1)
    hk hs (locallyIntegrable_const (1 : ℝ)) x v
  simp only [one_mul] at H
  rw [H]
  apply integral_congr_ae
  apply Filter.Eventually.of_forall
  intro y
  change fderiv ℝ (fun p => K.toFun (p,ε)) (x,y) (v,0) = _
  exact fderiv_productSection_first_apply K.smooth (x,y) ε (v,0)

end RothschildStein.S

-- Copyright (c) 2026 Scott Armstrong and Amélie Loher. All rights reserved.
-- Released under Apache 2.0 license as described in the file LICENSE.
module

public import RothschildStein.S.SmoothKernelTransfer
public import RothschildStein.S.SmoothKernelMeanDerivative
public import RothschildStein.S.ProductParameterDirections
public import RothschildStein.S.CompactDerivativeIntegrable

set_option autoImplicit false
set_option relaxedAutoImplicit false
set_option backward.isDefEq.respectTransparency false
@[expose] public section
noncomputable section
open Set MeasureTheory Function Filter Metric
open scoped BigOperators Topology ContDiff
namespace RothschildStein.S
variable {n : ℕ}

/-- The transfer mean is the coefficient-direction derivative
of the original mean; every y-divergence integrates to zero
(BB properties (a),(b), pp. 76,78). -/
theorem integral_smoothKernelTransfer (K : SmoothFriedrichsKernel n)
    (V : (Fin n → ℝ) → (Fin n → ℝ)) (hV : ContDiff ℝ (⊤ : ℕ∞) V)
    (ε : ℝ) (x : Fin n → ℝ) :
    (∫ y, (smoothKernelTransfer K V hV).family ε x y) =
      fderiv ℝ (fun x => ∫ y, K.family ε x y) x (V x) := by
  let L : (Fin n → ℝ) → ℝ :=
    fun y => fderiv ℝ K.toFun ((x,y),ε) ((V x,0),0)
  let F : Fin n → (Fin n → ℝ) → ℝ :=
    fun j y => hadamardCoefficient (fun z => V z j) ((x,y),ε) * K.toFun ((x,y),ε)
  have hprod (j : Fin n) : ContDiff ℝ (⊤ : ℕ∞)
      (fun p => hadamardCoefficient (fun z => V z j) p * K.toFun p) :=
    (contDiff_hadamardCoefficient ((contDiff_apply ℝ ℝ j).comp hV)).mul K.smooth
  have hF (j : Fin n) : ContDiff ℝ (⊤ : ℕ∞) (F j) :=
    (hprod j).comp ((contDiff_const.prodMk contDiff_id).prodMk contDiff_const)
  have hcF (j : Fin n) : HasCompactSupport (F j) := (K.section_compact ε x).mul_left
  have hcL : HasCompactSupport L := by
    apply (isCompact_closedBall (0 : Fin n → ℝ) 1).of_isClosed_subset isClosed_closure
    apply closure_minimal _ isClosed_closedBall
    intro y hy
    by_contra hn
    have hny : 1 < ‖y‖ := by simpa only [mem_closedBall,dist_zero_right,not_le] using hn
    apply hy
    change fderiv ℝ K.toFun ((x,y),ε) ((V x,0),0) = 0
    rw [fderiv_of_notMem_tsupport ℝ (fun ht => (not_le_of_gt hny) (K.tsupport_subset ht)),zero_apply]
  have hL : Continuous L :=
    (((K.smooth.fderiv_right (m := ((⊤ : ℕ∞) : ℕ∞ω)) (by simp)).continuous).comp
      ((continuous_const.prodMk continuous_id).prodMk continuous_const)).clm_apply continuous_const
  have hiL : Integrable L volume := hL.integrable_of_hasCompactSupport hcL
  have hiF (j : Fin n) := integrable_compact_fderiv_apply (hF j) (hcF j)
    (Hormander.Interface.basisVec j)
  have he (y : Fin n → ℝ) : (smoothKernelTransfer K V hV).family ε x y =
      L y + ∑ j : Fin n, fderiv ℝ (F j) y (Hormander.Interface.basisVec j) := by
    change L y + (∑ j : Fin n, fderiv ℝ
      (fun p => hadamardCoefficient (fun z => V z j) p * K.toFun p) ((x,y),ε)
        ((0,Hormander.Interface.basisVec j),0)) = _
    congr 1
    apply Finset.sum_congr rfl
    intro j hj
    exact (fderiv_xyParameter_second_apply (hprod j) ε x y
      (Hormander.Interface.basisVec j)).symm
  simp_rw [he]
  rw [integral_add hiL (integrable_finsetSum _ (fun j _ => hiF j)),
    integral_finsetSum _ (fun j _ => hiF j)]
  have hz : (∑ j : Fin n, ∫ y, fderiv ℝ (F j) y (Hormander.Interface.basisVec j)) = 0 :=
    Finset.sum_eq_zero (fun j _ => integral_compact_fderiv_eq_zero (hF j) (hcF j) _)
  rw [hz,add_zero]
  exact (fderiv_smoothKernelMean_apply K ε x (V x)).symm

/-- A kernel whose mean is locally constant has zero-mean
transfer, with no assumption about its mean outside the open patch
(BB p. 76). -/
theorem smoothKernelTransfer_mean_zero_of_constant_mean (K : SmoothFriedrichsKernel n)
    (V : (Fin n → ℝ) → (Fin n → ℝ)) (hV : ContDiff ℝ (⊤ : ℕ∞) V)
    {U : Set (Fin n → ℝ)} (hU : IsOpen U) (ε c : ℝ)
    (hmean : ∀ x ∈ U, (∫ y, K.family ε x y) = c)
    {x : Fin n → ℝ} (hx : x ∈ U) :
    (∫ y, (smoothKernelTransfer K V hV).family ε x y) = 0 := by
  rw [integral_smoothKernelTransfer]
  have hd : fderiv ℝ (fun x => ∫ y, K.family ε x y) x = 0 := by
    apply (hasFDerivAt_zero_of_eventually_const c ?_).fderiv
    filter_upwards [hU.mem_nhds hx] with z hz
    exact hmean z hz
  rw [hd,zero_apply]

end RothschildStein.S

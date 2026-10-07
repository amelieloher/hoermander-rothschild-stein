-- Copyright (c) 2026 Scott Armstrong and Amélie Loher. All rights reserved.
-- Released under Apache 2.0 license as described in the file LICENSE.
module

public import RothschildStein.S.SmoothFriedrichsKernels
public import Hormander.Interface.BasisVec

set_option autoImplicit false
set_option relaxedAutoImplicit false
set_option backward.isDefEq.respectTransparency false
@[expose] public section
noncomputable section
open Set MeasureTheory Function
open scoped BigOperators Topology ContDiff
namespace RothschildStein.S
variable {n : ℕ}

/-- Joint smooth form of the Friedrichs transfer: the x-field
applied to K plus the y-divergence of the Hadamard coefficient times K
(BB (2.11), p. 78). -/
def smoothKernelTransferValue (K : SmoothFriedrichsKernel n)
    (V : (Fin n → ℝ) → (Fin n → ℝ))
    (p : ((Fin n → ℝ) × (Fin n → ℝ)) × ℝ) : ℝ :=
  fderiv ℝ K.toFun p ((V p.1.1,0),0) +
    ∑ j : Fin n, fderiv ℝ
      (fun p => hadamardCoefficient (fun x => V x j) p * K.toFun p) p
        ((0,Hormander.Interface.basisVec j),0)

/-- Joint smoothness is preserved by Friedrichs transfer
(BB pp. 76,78–79; preferred Hadamard encoding). -/
theorem contDiff_smoothKernelTransferValue (K : SmoothFriedrichsKernel n)
    (V : (Fin n → ℝ) → (Fin n → ℝ)) (hV : ContDiff ℝ (⊤ : ℕ∞) V) :
    ContDiff ℝ (⊤ : ℕ∞) (smoothKernelTransferValue K V) := by
  have hv : ContDiff ℝ (⊤ : ℕ∞)
      (fun p : ((Fin n → ℝ) × (Fin n → ℝ)) × ℝ =>
        ((V p.1.1,(0 : Fin n → ℝ)),(0 : ℝ))) :=
    (((hV.comp contDiff_fst.fst).prodMk contDiff_const).prodMk contDiff_const)
  have hfirst := (K.smooth.fderiv_right (m := ((⊤ : ℕ∞) : ℕ∞ω)) (by simp)).clm_apply hv
  apply hfirst.add
  apply ContDiff.sum
  intro j hj
  have hb : ContDiff ℝ (⊤ : ℕ∞) (fun x => V x j) := (contDiff_apply ℝ ℝ j).comp hV
  have hp := (contDiff_hadamardCoefficient hb).mul K.smooth
  exact (hp.fderiv_right (m := ((⊤ : ℕ∞) : ℕ∞ω)) (by simp)).clm_apply contDiff_const

/-- Transfer never enlarges the unit y-support
(BB properties (a),(b), pp. 76,78). -/
theorem smoothKernelTransferValue_vanish (K : SmoothFriedrichsKernel n)
    (V : (Fin n → ℝ) → (Fin n → ℝ))
    (p : ((Fin n → ℝ) × (Fin n → ℝ)) × ℝ) (hp : 1 < ‖p.1.2‖) :
    smoothKernelTransferValue K V p = 0 := by
  have hn : p ∉ tsupport K.toFun :=
    fun ht => (not_le_of_gt hp) (K.tsupport_subset ht)
  unfold smoothKernelTransferValue
  rw [fderiv_of_notMem_tsupport ℝ hn,zero_apply,zero_add]
  apply Finset.sum_eq_zero
  intro j hj
  have hn' : p ∉ tsupport
      (fun p => hadamardCoefficient (fun x => V x j) p * K.toFun p) :=
    fun ht => hn (tsupport_mul_subset_right ht)
  rw [fderiv_of_notMem_tsupport ℝ hn',zero_apply]

/-- The constructed kernel class is closed under transfer.
Its bounded-kernel certificate is supplied by `toBounded` on each compact
patch (BB (2.11), pp. 78–79). -/
def smoothKernelTransfer (K : SmoothFriedrichsKernel n)
    (V : (Fin n → ℝ) → (Fin n → ℝ)) (hV : ContDiff ℝ (⊤ : ℕ∞) V) :
    SmoothFriedrichsKernel n where
  toFun := smoothKernelTransferValue K V
  smooth := contDiff_smoothKernelTransferValue K V hV
  vanish := smoothKernelTransferValue_vanish K V

end RothschildStein.S

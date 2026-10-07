-- Copyright (c) 2026 Scott Armstrong and Amélie Loher. All rights reserved.
-- Released under Apache 2.0 license as described in the file LICENSE.
module

public import RothschildStein.S.RescaledKernelChainRule
public import RothschildStein.S.TransferValueExpansion

set_option autoImplicit false
set_option relaxedAutoImplicit false
set_option backward.isDefEq.respectTransparency false
@[expose] public section
noncomputable section
open Set MeasureTheory Function
open scoped BigOperators Topology ContDiff
namespace RothschildStein.S
variable {n : ℕ}

/-- The difference of the base-point derivative and the transposed
integration-variable derivative is precisely the rescaled transfer kernel
(BB (2.11), p. 78; chain-rule). -/
theorem rescaledKernel_transfer_identity (K : SmoothFriedrichsKernel n)
    (V : (Fin n → ℝ) → (Fin n → ℝ)) (hV : ContDiff ℝ (⊤ : ℕ∞) V)
    {ε : ℝ} (hε : ε ≠ 0) (x z : Fin n → ℝ) :
    fieldDerivative V (fun a => friedrichsRescaledKernel K.family ε a z) x -
      fieldTranspose V (friedrichsRescaledKernel K.family ε x) z =
      friedrichsRescaledKernel (smoothKernelTransfer K V hV).family ε x z := by
  let y := ε⁻¹ • (z-x)
  have hz : x+ε • y = z := by
    dsimp [y]
    rw [smul_smul,mul_inv_cancel₀ hε,one_smul]
    abel
  have hd : DifferentiableAt ℝ (friedrichsRescaledKernel K.family ε x) z :=
    (((contDiff_friedrichsRescaledKernel K ε).comp
      (contDiff_const.prodMk contDiff_id)).differentiable (by simp)).differentiableAt
  rw [fieldTranspose_formula V _ z
    ((hV.differentiable (by simp)).differentiableAt) hd]
  unfold fieldDerivative
  rw [fderiv_friedrichsRescaledKernel_x,fderiv_friedrichsRescaledKernel_z]
  unfold friedrichsRescaledKernel
  rw [smoothKernelTransfer_family_eq_raw K V hV hε,
    friedrichsTransferValue_expansion K V hV hε,hz]
  have hk : ContDiff ℝ (⊤ : ℕ∞) (uncurry (K.family ε)) :=
    K.smooth.comp ((contDiff_fst.prodMk contDiff_snd).prodMk contDiff_const)
  have hx' : fieldDerivative V (fun a => K.family ε a y) x =
      fderiv ℝ (uncurry (K.family ε)) (x,y) (V x,0) := by
    simpa only [fieldDerivative,uncurry] using!
      fderiv_productSection_first_apply hk x y (V x)
  have hy' : fderiv ℝ (K.family ε x) y (ε⁻¹ • (V z-V x)) =
      fderiv ℝ (uncurry (K.family ε)) (x,y) (0,ε⁻¹ • (V z-V x)) := by
    simpa only [uncurry] using!
      fderiv_productSection_second_apply hk x y (ε⁻¹ • (V z-V x))
  rw [hx',hy']
  have he : (V x,-(ε⁻¹ • V x)) + ((0 : Fin n → ℝ),ε⁻¹ • V z) =
      (V x,0) + ((0 : Fin n → ℝ),ε⁻¹ • (V z-V x)) := by
    ext j <;> simp [smul_sub]
    abel
  have hm := congrArg (fderiv ℝ (uncurry (K.family ε)) (x,y)) he
  simp only [map_add] at hm
  change (ε^n)⁻¹ * fderiv ℝ (uncurry (K.family ε)) (x,y) (V x,-(ε⁻¹ • V x)) -
    (-( (ε^n)⁻¹ * fderiv ℝ (uncurry (K.family ε)) (x,y) (0,ε⁻¹ • V z)) -
      ((ε^n)⁻¹ * K.family ε x y) * Hormander.Interface.euclideanDivergence V z) = _
  have hm' := congrArg (fun t : ℝ => (ε^n)⁻¹ * t) hm
  simp only [mul_add] at hm'
  dsimp [y] at *
  linarith only [hm']

end RothschildStein.S

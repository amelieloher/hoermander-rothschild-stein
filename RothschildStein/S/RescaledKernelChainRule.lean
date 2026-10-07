-- Copyright (c) 2026 Scott Armstrong and Amélie Loher. All rights reserved.
-- Released under Apache 2.0 license as described in the file LICENSE.
module

public import RothschildStein.S.RescaledKernelGeometry
public import RothschildStein.S.ProductSectionDerivative
public import Mathlib.Analysis.Calculus.FDeriv.Mul

set_option autoImplicit false
set_option relaxedAutoImplicit false
set_option backward.isDefEq.respectTransparency false
@[expose] public section
noncomputable section
open Set MeasureTheory Function
open scoped Topology ContDiff
namespace RothschildStein.S
variable {n : ℕ}

/-- The x-direction derivative of the rescaled kernel includes
the negative displacement derivative (BB (2.11), p. 78). -/
theorem fderiv_friedrichsRescaledKernel_x (K : SmoothFriedrichsKernel n)
    (ε : ℝ) (x z v : Fin n → ℝ) :
    fderiv ℝ (fun a => friedrichsRescaledKernel K.family ε a z) x v =
      (ε^n)⁻¹ * fderiv ℝ (uncurry (K.family ε)) (x,ε⁻¹ • (z-x))
        (v,-(ε⁻¹ • v)) := by
  have hk : ContDiff ℝ (⊤ : ℕ∞) (uncurry (K.family ε)) :=
    K.smooth.comp ((contDiff_fst.prodMk contDiff_snd).prodMk contDiff_const)
  have ha := (hasFDerivAt_id (𝕜 := ℝ) x).prodMk
    (((hasFDerivAt_id (𝕜 := ℝ) x).const_sub z).const_smul ε⁻¹)
  have hd := ((hk.differentiable (by simp)).differentiableAt.hasFDerivAt.comp x ha).const_mul (ε^n)⁻¹
  simp only [Function.comp_def] at hd
  change fderiv ℝ (fun a => (ε^n)⁻¹ * K.family ε a (ε⁻¹ • (z-a))) x v = _
  simpa only [uncurry, id_eq, Pi.smul_apply, smul_apply,
    ContinuousLinearMap.comp_apply, ContinuousLinearMap.prod_apply,
    ContinuousLinearMap.id_apply, neg_apply, neg_smul,
    smul_neg, zero_apply, smul_eq_mul] using! congrArg (fun A => A v) hd.fderiv

/-- The integration-variable derivative of the rescaled kernel
contains precisely the inverse scale factor (BB (2.11), p. 78). -/
theorem fderiv_friedrichsRescaledKernel_z (K : SmoothFriedrichsKernel n)
    (ε : ℝ) (x z v : Fin n → ℝ) :
    fderiv ℝ (friedrichsRescaledKernel K.family ε x) z v =
      (ε^n)⁻¹ * fderiv ℝ (uncurry (K.family ε)) (x,ε⁻¹ • (z-x))
        (0,ε⁻¹ • v) := by
  have hk : ContDiff ℝ (⊤ : ℕ∞) (uncurry (K.family ε)) :=
    K.smooth.comp ((contDiff_fst.prodMk contDiff_snd).prodMk contDiff_const)
  have ha := (hasFDerivAt_const (𝕜 := ℝ) x z).prodMk
    (((hasFDerivAt_id (𝕜 := ℝ) z).sub_const x).const_smul ε⁻¹)
  have hd := ((hk.differentiable (by simp)).differentiableAt.hasFDerivAt.comp z ha).const_mul (ε^n)⁻¹
  simp only [Function.comp_def] at hd
  change fderiv ℝ (fun z => (ε^n)⁻¹ * K.family ε x (ε⁻¹ • (z-x))) z v = _
  simpa only [uncurry, id_eq, Pi.smul_apply, smul_apply,
    ContinuousLinearMap.comp_apply, ContinuousLinearMap.prod_apply,
    ContinuousLinearMap.id_apply, neg_apply, neg_smul,
    smul_neg, zero_apply, smul_eq_mul] using! congrArg (fun A => A v) hd.fderiv

end RothschildStein.S

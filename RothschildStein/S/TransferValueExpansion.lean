-- Copyright (c) 2026 Scott Armstrong and Amélie Loher. All rights reserved.
-- Released under Apache 2.0 license as described in the file LICENSE.
module

public import RothschildStein.S.SmoothKernelTransferFormula
public import RothschildStein.S.HadamardFirstDerivative
public import RothschildStein.S.Transposes
public import RothschildStein.S.ProductSectionDerivative

set_option autoImplicit false
set_option relaxedAutoImplicit false
set_option backward.isDefEq.respectTransparency false
@[expose] public section
noncomputable section
open Set MeasureTheory Function
open scoped BigOperators Topology ContDiff
namespace RothschildStein.S
variable {n : ℕ}

/-- Expanding the y-divergence identifies the transfer
kernel's drift in the displacement variable and the divergence term
(BB (2.11), p. 78). -/
theorem friedrichsTransferValue_expansion (K : SmoothFriedrichsKernel n)
    (V : (Fin n → ℝ) → (Fin n → ℝ)) (hV : ContDiff ℝ (⊤ : ℕ∞) V)
    {ε : ℝ} (hε : ε ≠ 0) (x y : Fin n → ℝ) :
    friedrichsTransferValue K.family V ε x y =
      fieldDerivative V (fun a => K.family ε a y) x +
      fderiv ℝ (K.family ε x) y (ε⁻¹ • (V (x+ε • y)-V x)) +
      K.family ε x y * Hormander.Interface.euclideanDivergence V (x+ε • y) := by
  have hd : DifferentiableAt ℝ (K.family ε x) y :=
    ((K.section_smooth ε x).differentiable (by simp)).differentiableAt
  have hq (j : Fin n) : DifferentiableAt ℝ
      (coefficientDifferenceQuotient (fun z => V z j) ε x) y := by
    have hv : ContDiff ℝ (⊤ : ℕ∞) (fun z => V z j) := (contDiff_apply ℝ ℝ j).comp hV
    exact ((contDiff_const.mul
      ((hv.comp (contDiff_const.add (contDiff_id.const_smul ε))).sub contDiff_const)).differentiable
        (by simp)).differentiableAt
  have hprod (j : Fin n) :
      fderiv ℝ (fun y => coefficientDifferenceQuotient (fun z => V z j) ε x y * K.family ε x y)
        y (Hormander.Interface.basisVec j) =
      coefficientDifferenceQuotient (fun z => V z j) ε x y *
        fderiv ℝ (K.family ε x) y (Hormander.Interface.basisVec j) +
      K.family ε x y * fderiv ℝ (coefficientDifferenceQuotient (fun z => V z j) ε x)
        y (Hormander.Interface.basisVec j) := by
    simpa only [Pi.mul_apply,add_apply,smul_apply,smul_eq_mul] using!
      congrArg (fun A => A (Hormander.Interface.basisVec j)) (fderiv_mul (hq j) hd)
  unfold friedrichsTransferValue
  simp_rw [hprod]
  rw [Finset.sum_add_distrib]
  have h1 : (∑ j : Fin n, coefficientDifferenceQuotient (fun z => V z j) ε x y *
      fderiv ℝ (K.family ε x) y (Hormander.Interface.basisVec j)) =
      fderiv ℝ (K.family ε x) y (ε⁻¹ • (V (x+ε • y)-V x)) := by
    rw [differential_coordinates]
    rfl
  have h2 : (∑ j : Fin n, K.family ε x y *
      fderiv ℝ (coefficientDifferenceQuotient (fun z => V z j) ε x) y
        (Hormander.Interface.basisVec j)) =
      K.family ε x y * Hormander.Interface.euclideanDivergence V (x+ε • y) := by
    rw [← Finset.mul_sum]
    congr 1
    apply Finset.sum_congr rfl
    intro j hj
    have hv : ContDiff ℝ (⊤ : ℕ∞) (fun z => V z j) := (contDiff_apply ℝ ℝ j).comp hV
    have heq : fderiv ℝ (coefficientDifferenceQuotient (fun z => V z j) ε x) y
        (Hormander.Interface.basisVec j) =
        fderiv ℝ (fun z => V z j) (x+ε • y) (Hormander.Interface.basisVec j) :=
      coefficientDifferenceQuotient_fderiv_y hv hε x y (Hormander.Interface.basisVec j)
    rw [heq]
    have he := (hasFDerivAt_apply (𝕜 := ℝ) j (V (x+ε • y))).comp (x+ε • y)
      ((hV.differentiable (by simp)).differentiableAt.hasFDerivAt)
    simp only [Function.comp_def] at he
    simpa only [ContinuousLinearMap.comp_apply,ContinuousLinearMap.proj_apply] using!
      congrArg (fun A => A (Hormander.Interface.basisVec j)) he.fderiv
  rw [h1,h2]
  ring

end RothschildStein.S

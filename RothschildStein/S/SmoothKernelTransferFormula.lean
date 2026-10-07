-- Copyright (c) 2026 Scott Armstrong and Amélie Loher. All rights reserved.
-- Released under Apache 2.0 license as described in the file LICENSE.
module

public import RothschildStein.S.SmoothKernelTransfer
public import RothschildStein.S.ProductParameterDirections
public import RothschildStein.Definitions.fieldDerivative

set_option autoImplicit false
set_option relaxedAutoImplicit false
@[expose] public section
noncomputable section
open Set MeasureTheory Function
open scoped BigOperators
namespace RothschildStein.S
variable {n : ℕ}

/-- The unbundled positive-ε transfer formula: X in the x variable
plus the y-divergence of coefficient difference quotients times K
(BB (2.11), p. 78). -/
def friedrichsTransferValue
    (K : ℝ → (Fin n → ℝ) → (Fin n → ℝ) → ℝ)
    (V : (Fin n → ℝ) → (Fin n → ℝ)) (ε : ℝ) (x y : Fin n → ℝ) : ℝ :=
  fieldDerivative V (fun x => K ε x y) x +
    ∑ j : Fin n, fderiv ℝ
      (fun y => coefficientDifferenceQuotient (fun z => V z j) ε x y * K ε x y)
      y (Hormander.Interface.basisVec j)

/-- The joint Hadamard transfer equals the coefficient-quotient formula at every nonzero ε
(BB (2.11), p. 78; smooth parameter dependence). -/
theorem smoothKernelTransfer_family_eq_raw (K : SmoothFriedrichsKernel n)
    (V : (Fin n → ℝ) → (Fin n → ℝ)) (hV : ContDiff ℝ (⊤ : ℕ∞) V)
    {ε : ℝ} (hε : ε ≠ 0) (x y : Fin n → ℝ) :
    (smoothKernelTransfer K V hV).family ε x y =
      friedrichsTransferValue K.family V ε x y := by
  unfold friedrichsTransferValue fieldDerivative
  rw [show (fun x => K.family ε x y) = (fun x => K.toFun ((x,y),ε)) from rfl,
    fderiv_xyParameter_first_apply K.smooth ε x y (V x)]
  change fderiv ℝ K.toFun ((x,y),ε) ((V x,0),0) + _ =
    fderiv ℝ K.toFun ((x,y),ε) ((V x,0),0) + _
  congr 1
  apply Finset.sum_congr rfl
  intro j hj
  have hb : ContDiff ℝ (⊤ : ℕ∞) (fun z => V z j) := (contDiff_apply ℝ ℝ j).comp hV
  have hf : ContDiff ℝ (⊤ : ℕ∞)
      (fun p => hadamardCoefficient (fun z => V z j) p * K.toFun p) :=
    (contDiff_hadamardCoefficient hb).mul K.smooth
  have he : (fun y => coefficientDifferenceQuotient (fun z => V z j) ε x y * K.family ε x y) =
      fun y => hadamardCoefficient (fun z => V z j) ((x,y),ε) * K.toFun ((x,y),ε) := by
    funext y
    rw [coefficientDifferenceQuotient_eq_hadamard hb hε]
    rfl
  rw [he,fderiv_xyParameter_second_apply hf ε x y (Hormander.Interface.basisVec j)]

end RothschildStein.S

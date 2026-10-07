-- Copyright (c) 2026 Scott Armstrong and Amélie Loher. All rights reserved.
-- Released under Apache 2.0 license as described in the file LICENSE.
module

public import RothschildStein.G2.CoefficientWeights

set_option autoImplicit false
set_option relaxedAutoImplicit false
set_option backward.isDefEq.respectTransparency false

@[expose] public section
noncomputable section
namespace RothschildStein.G2
open MvPolynomial
variable {N : ℕ} (G : HomogeneousGroup N)

private theorem polynomialProduct_swap (P : Fin N → MvPolynomial (Fin N ⊕ Fin N) ℝ)
    (x y : Fin N → ℝ) :
    polynomialProduct (fun k => rename Sum.swap (P k)) x y = polynomialProduct P y x := by
  ext k
  simp [polynomialProduct, eval_rename]

/-- Reversing the group law exchanges left and right invariant constructions
(BB Proposition 3.26, p. 109). -/
def oppositeGroup : HomogeneousGroup N where
  dimension_pos := G.dimension_pos
  weight := G.weight
  weight_pos := G.weight_pos
  weight_mono := G.weight_mono
  productPolynomial k := rename Sum.swap (G.productPolynomial k)
  inversePolynomial := G.inversePolynomial
  zero_left x := by rw [polynomialProduct_swap]; exact G.zero_right x
  zero_right x := by rw [polynomialProduct_swap]; exact G.zero_left x
  assoc x y z := by
    simp only [polynomialProduct_swap]
    exact (G.assoc z y x).symm
  inverse_left x := by rw [polynomialProduct_swap]; exact G.inverse_right x
  inverse_right x := by rw [polynomialProduct_swap]; exact G.inverse_left x
  dilation_product t ht x y := by
    simp only [polynomialProduct_swap]
    exact G.dilation_product t ht y x

/-- Multiplication in the opposite group is reversed original multiplication. -/
theorem oppositeGroup_mul (x y : Fin N → ℝ) : (oppositeGroup G).mul x y = G.mul y x := by
  exact polynomialProduct_swap G.productPolynomial x y

/-- Dilation is unchanged by reversing the group law. -/
theorem oppositeGroup_dilate (t : ℝ) : (oppositeGroup G).dilate t = G.dilate t := rfl

/-- Left fields of the opposite group are right fields of the original group (BB p. 109). -/
theorem oppositeGroup_leftField (v : Fin N → ℝ) :
    leftField (oppositeGroup G) v = rightField G v := by
  funext x
  have he : (oppositeGroup G).mul x = fun y => G.mul y x :=
    funext (oppositeGroup_mul G x)
  simp [leftField, rightField, he]

/-- The opposite-group coefficients are the right canonical coefficients (BB p. 111). -/
theorem oppositeGroup_leftCoefficient (i k : Fin N) :
    leftCoefficient (oppositeGroup G) i k = rightCoefficient G i k := by
  apply MvPolynomial.funext
  intro x
  rw [← canonicalField_coordinate, canonicalField_eq_leftField,
    oppositeGroup_leftField, rightField_coordinate]

end RothschildStein.G2

-- Copyright (c) 2026 Scott Armstrong and Amélie Loher. All rights reserved.
-- Released under Apache 2.0 license as described in the file LICENSE.
module

public import RothschildStein.G2.NormConstruction

set_option autoImplicit false
set_option relaxedAutoImplicit false
@[expose] public section
noncomputable section
open Set MeasureTheory
open scoped BigOperators Topology
namespace RothschildStein.S
variable {n : ℕ}

/-- The additive coordinate group with unit weights is a homogeneous group (BB Lemma 2.8, p. 72). -/
def additiveCoordinateGroup (hn : 0 < n) : HomogeneousGroup n where
  dimension_pos := hn
  weight := fun _ => 1
  weight_pos := fun _ => Nat.zero_lt_one
  weight_mono := fun _ _ _ => le_rfl
  productPolynomial := fun j => MvPolynomial.X (Sum.inl j) + MvPolynomial.X (Sum.inr j)
  inversePolynomial := fun j => -MvPolynomial.X j
  zero_left := by intro x; ext j; simp [polynomialProduct]
  zero_right := by intro x; ext j; simp [polynomialProduct]
  assoc := by intro x y z; ext j; simp [polynomialProduct,add_assoc]
  inverse_left := by intro x; ext j; simp [polynomialProduct]
  inverse_right := by intro x; ext j; simp [polynomialProduct]
  dilation_product := by intro t _ x y; ext j; simp [coordinateDilation,polynomialProduct,mul_add]

/-- The additive specialization has the ordinary addition law
(BB Lemma 2.8, p. 72). -/
theorem additiveCoordinateGroup_mul (hn : 0 < n) (x y : Fin n → ℝ) :
    (additiveCoordinateGroup hn).mul x y = x+y := by
  ext j
  simp [HomogeneousGroup.mul,additiveCoordinateGroup,polynomialProduct]

/-- The additive specialization has ordinary negation as inverse
(BB Lemma 2.8, p. 72). -/
theorem additiveCoordinateGroup_inv (hn : 0 < n) (x : Fin n → ℝ) :
    (additiveCoordinateGroup hn).inv x = -x := by
  ext j
  simp [HomogeneousGroup.inv,additiveCoordinateGroup]

/-- Weight-one dilation is scalar multiplication
(BB Lemma 2.8, p. 72). -/
theorem additiveCoordinateGroup_dilate (hn : 0 < n) (t : ℝ) (x : Fin n → ℝ) :
    (additiveCoordinateGroup hn).dilate t x = t • x := by
  ext j
  simp [HomogeneousGroup.dilate,additiveCoordinateGroup,coordinateDilation]

/-- The coordinate norm is a homogeneous norm for the additive
specialization (BB Lemma 2.8, p. 72). -/
def additiveCoordinateNorm (hn : 0 < n) : RothschildStein.G2.HomogeneousNorm (additiveCoordinateGroup hn) :=
  { toFun := norm
    gauge := ⟨continuous_norm, norm_nonneg, fun x => norm_eq_zero,
      fun t ht x => by rw [additiveCoordinateGroup_dilate,norm_smul,Real.norm_of_nonneg ht.le]⟩
    c := 1
    one_le_c := le_rfl
    inv_le := fun x => by rw [additiveCoordinateGroup_inv,norm_neg,one_mul]
    mul_le := fun x y => by rw [additiveCoordinateGroup_mul,one_mul]; exact norm_add_le x y }

end RothschildStein.S

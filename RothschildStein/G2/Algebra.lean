-- Copyright (c) 2026 Scott Armstrong and Amélie Loher. All rights reserved.
-- Released under Apache 2.0 license as described in the file LICENSE.
module

public import RothschildStein.Definitions.HomogeneousGroup.mul
public import RothschildStein.Definitions.HomogeneousGroup.inv
public import RothschildStein.Definitions.HomogeneousGroup.dilate
public import Mathlib.Topology.Algebra.MvPolynomial

set_option autoImplicit false
set_option relaxedAutoImplicit false

@[expose] public section
noncomputable section
namespace RothschildStein.G2

variable {N : ℕ} (G : HomogeneousGroup N)

/-- The origin is a left identity (BB Definition 3.1, p. 94). -/
@[simp] theorem zero_mul (x : Fin N → ℝ) : G.mul 0 x = x := G.zero_left x

/-- The origin is a right identity (BB Definition 3.1, p. 94). -/
@[simp] theorem mul_zero (x : Fin N → ℝ) : G.mul x 0 = x := G.zero_right x

/-- Associativity of the polynomial law (BB Definition 3.1, p. 94). -/
theorem mul_assoc (x y z : Fin N → ℝ) : G.mul (G.mul x y) z = G.mul x (G.mul y z) :=
  G.assoc x y z

/-- The inverse is a left inverse (BB Proposition 3.7, p. 98). -/
@[simp] theorem inv_mul (x : Fin N → ℝ) : G.mul (G.inv x) x = 0 := G.inverse_left x

/-- The inverse is a right inverse (BB Proposition 3.7, p. 98). -/
@[simp] theorem mul_inv (x : Fin N → ℝ) : G.mul x (G.inv x) = 0 := G.inverse_right x

/-- Uniqueness of a right inverse (BB Proposition 3.7, p. 98). -/
theorem inv_unique {x y : Fin N → ℝ} (h : G.mul x y = 0) : y = G.inv x := by
  calc
    y = G.mul 0 y := (zero_mul G y).symm
    _ = G.mul (G.mul (G.inv x) x) y := by rw [inv_mul]
    _ = G.mul (G.inv x) (G.mul x y) := mul_assoc G _ _ _
    _ = G.inv x := by rw [h, mul_zero]

/-- Inversion is involutive (BB Proposition 3.7, p. 98). -/
@[simp] theorem inv_inv (x : Fin N → ℝ) : G.inv (G.inv x) = x :=
  (inv_unique G (inv_mul G x)).symm

/-- Inversion fixes the identity (BB Proposition 3.7, p. 98). -/
@[simp] theorem inv_zero : G.inv 0 = 0 := (inv_unique G (zero_mul G 0)).symm

/-- Inversion reverses products (BB Proposition 3.7, p. 98). -/
theorem inv_product (x y : Fin N → ℝ) : G.inv (G.mul x y) = G.mul (G.inv y) (G.inv x) := by
  apply Eq.symm
  apply inv_unique G
  calc
    G.mul (G.mul x y) (G.mul (G.inv y) (G.inv x)) =
        G.mul x (G.mul y (G.mul (G.inv y) (G.inv x))) := mul_assoc G _ _ _
    _ = G.mul x (G.mul (G.mul y (G.inv y)) (G.inv x)) := by rw [mul_assoc]
    _ = 0 := by rw [mul_inv, zero_mul, mul_inv]

/-- Coordinate dilations compose multiplicatively (BB Definition 3.2, p. 95). -/
theorem dilate_dilate (s t : ℝ) (x : Fin N → ℝ) :
    G.dilate s (G.dilate t x) = G.dilate (s * t) x := by
  ext j
  simp only [HomogeneousGroup.dilate, coordinateDilation, mul_pow]
  ring

/-- The unit dilation is the identity (BB Definition 3.2, p. 95). -/
@[simp] theorem dilate_one (x : Fin N → ℝ) : G.dilate 1 x = x := by
  ext j
  simp [HomogeneousGroup.dilate, coordinateDilation]

/-- Every dilation fixes the origin (BB Definition 3.2, p. 95). -/
@[simp] theorem dilate_zero (t : ℝ) : G.dilate t 0 = 0 := by
  ext j
  simp [HomogeneousGroup.dilate, coordinateDilation]

/-- The zero dilation collapses to the origin, using positive weights (BB p. 95). -/
@[simp] theorem zero_dilate (x : Fin N → ℝ) : G.dilate 0 x = 0 := by
  ext j
  simp [HomogeneousGroup.dilate, coordinateDilation, Nat.ne_of_gt (G.weight_pos j)]

/-- A nonzero dilation has inverse the reciprocal dilation (BB Proposition 3.7, p. 98). -/
theorem dilate_inv_dilate {t : ℝ} (ht : t ≠ 0) (x : Fin N → ℝ) :
    G.dilate t⁻¹ (G.dilate t x) = x := by rw [dilate_dilate, inv_mul_cancel₀ ht, dilate_one]

/-- Positive dilations preserve multiplication (BB Definition 3.2, p. 95). -/
theorem dilate_product {t : ℝ} (ht : 0 < t) (x y : Fin N → ℝ) :
    G.dilate t (G.mul x y) = G.mul (G.dilate t x) (G.dilate t y) :=
  G.dilation_product t ht x y

/-- Inversion commutes with positive dilations (BB Proposition 3.7, p. 98). -/
theorem inv_dilate {t : ℝ} (ht : 0 < t) (x : Fin N → ℝ) :
    G.inv (G.dilate t x) = G.dilate t (G.inv x) := by
  apply Eq.symm
  apply inv_unique G
  rw [← dilate_product G ht, mul_inv, dilate_zero]

/-- Dilation commutes with reflection without the INV hypothesis (BB p. 98). -/
theorem dilate_neg (t : ℝ) (x : Fin N → ℝ) : G.dilate t (-x) = -G.dilate t x := by
  ext j
  simp [HomogeneousGroup.dilate, coordinateDilation]

/-- The optional INV condition, separate from the group definition (BB p. 98). -/
def HasNegInverse : Prop := ∀ x : Fin N → ℝ, G.inv x = -x

/-- The polynomial multiplication is continuous (BB Theorem 3.6, p. 96). -/
theorem continuous_mul : Continuous (fun p : (Fin N → ℝ) × (Fin N → ℝ) => G.mul p.1 p.2) := by
  apply continuous_pi
  intro j
  exact (MvPolynomial.continuous_eval (p := G.productPolynomial j)).comp
    (continuous_pi fun i => Sum.casesOn i
      (fun j => (continuous_apply j).comp continuous_fst)
      (fun j => (continuous_apply j).comp continuous_snd))

/-- The polynomial inverse is continuous (BB Proposition 3.7, p. 98). -/
theorem continuous_inv : Continuous G.inv :=
  continuous_pi fun j => MvPolynomial.continuous_eval (p := G.inversePolynomial j)

end RothschildStein.G2

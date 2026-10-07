-- Copyright (c) 2026 Scott Armstrong and Amélie Loher. All rights reserved.
-- Released under Apache 2.0 license as described in the file LICENSE.
module

public import RothschildStein.G2.QuasiBounds

set_option autoImplicit false
set_option relaxedAutoImplicit false
@[expose] public section
noncomputable section
open Set
namespace RothschildStein.G2
variable {N : ℕ} (G : HomogeneousGroup N)

/-- Gauge quasidistance, with BB's order of arguments (BB Def 3.15, p. 103). -/
def gaugeDistance (ν : (Fin N → ℝ) → ℝ) (x y : Fin N → ℝ) : ℝ := ν (G.mul (G.inv y) x)

/-- Open gauge ball (BB Def 3.18, p. 104). -/
def gaugeBall (ν : (Fin N → ℝ) → ℝ) (x : Fin N → ℝ) (r : ℝ) : Set (Fin N → ℝ) :=
  {y | gaugeDistance G ν y x < r}

/-- Closed gauge ball (BB Thm 3.20, p. 105). -/
def gaugeClosedBall (ν : (Fin N → ℝ) → ℝ) (x : Fin N → ℝ) (r : ℝ) : Set (Fin N → ℝ) :=
  {y | gaugeDistance G ν y x ≤ r}

private theorem norm_assoc (x y z : Fin N → ℝ) :
    G.mul (G.mul x y) z = G.mul x (G.mul y z) := G.assoc x y z
private theorem norm_mul_zero (x : Fin N → ℝ) : G.mul x 0 = x := G.zero_right x
private theorem norm_zero_mul (x : Fin N → ℝ) : G.mul 0 x = x := G.zero_left x
private theorem norm_inv_mul (x : Fin N → ℝ) : G.mul (G.inv x) x = 0 := G.inverse_left x
private theorem norm_mul_inv (x : Fin N → ℝ) : G.mul x (G.inv x) = 0 := G.inverse_right x

/-- Zero detection for gauge quasidistance (BB Prop 3.16, p. 103). -/
theorem gaugeDistance_eq_zero_iff {ν : (Fin N → ℝ) → ℝ}
    (hν : G.IsHomogeneousGauge ν) (x y : Fin N → ℝ) :
    gaugeDistance G ν x y = 0 ↔ x = y := by
  rw [gaugeDistance, hν.2.2.1]
  constructor
  · intro h
    calc
      x = G.mul 0 x := (norm_zero_mul G x).symm
      _ = G.mul (G.mul y (G.inv y)) x := by rw [norm_mul_inv]
      _ = G.mul y (G.mul (G.inv y) x) := norm_assoc G _ _ _
      _ = y := by rw [h, norm_mul_zero]
  · rintro rfl
    exact norm_inv_mul G x

/-- Gauge quasitriangle inequality (BB Prop 3.16, p. 103). -/
theorem gaugeDistance_triangle (ν : HomogeneousNorm G) (x y z : Fin N → ℝ) :
    gaugeDistance G ν x y ≤ ν.c *
      (gaugeDistance G ν x z + gaugeDistance G ν z y) := by
  have he : G.mul (G.mul (G.inv y) z) (G.mul (G.inv z) x) = G.mul (G.inv y) x := by
    rw [norm_assoc, ← norm_assoc G z, norm_mul_inv, norm_zero_mul]
  unfold gaugeDistance
  rw [← he]
  simpa [add_comm] using ν.mul_le (G.mul (G.inv y) z) (G.mul (G.inv z) x)

/-- Left invariance follows from the product and involution identities (BB Proposition 3.16, p. 103). -/
theorem gaugeDistance_leftInvariant_of_groupIdentities
    (hp : ∀ x y, G.inv (G.mul x y) = G.mul (G.inv y) (G.inv x))
    (ν : (Fin N → ℝ) → ℝ) (x y z : Fin N → ℝ) :
    gaugeDistance G ν (G.mul z x) (G.mul z y) = gaugeDistance G ν x y := by
  unfold gaugeDistance
  rw [hp, norm_assoc, ← norm_assoc G (G.inv z), norm_inv_mul, norm_zero_mul]

/-- Dilation homogeneity follows from the exact inversion and dilation identities (BB Proposition 3.16, p. 103). -/
theorem gaugeDistance_dilate_of_groupIdentities
    (hi : ∀ t : ℝ, 0 < t → ∀ x, G.inv (G.dilate t x) = G.dilate t (G.inv x))
    {ν : (Fin N → ℝ) → ℝ} (hν : G.IsHomogeneousGauge ν)
    (t : ℝ) (ht : 0 < t) (x y : Fin N → ℝ) :
    gaugeDistance G ν (G.dilate t x) (G.dilate t y) = t * gaugeDistance G ν x y := by
  unfold gaugeDistance
  rw [hi t ht]
  have hd : G.dilate t (G.mul (G.inv y) x) =
      G.mul (G.dilate t (G.inv y)) (G.dilate t x) := G.dilation_product t ht _ _
  rw [← hd, hν.2.2.2 t ht]

/-- Symmetric norms give symmetric quasidistances by the inverse identities (BB Proposition 3.16, p. 103). -/
theorem gaugeDistance_symmetric_of_groupIdentities
    (hi : ∀ x, G.inv (G.inv x) = x)
    (hp : ∀ x y, G.inv (G.mul x y) = G.mul (G.inv y) (G.inv x))
    (ν : HomogeneousNorm G) (hν : ν.Symmetric) (x y : Fin N → ℝ) :
    gaugeDistance G ν y x = gaugeDistance G ν x y := by
  have he : G.inv (G.mul (G.inv y) x) = G.mul (G.inv x) y := by rw [hp, hi]
  unfold gaugeDistance
  rw [← he, hν]

end RothschildStein.G2

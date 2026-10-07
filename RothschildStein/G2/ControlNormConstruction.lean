-- Copyright (c) 2026 Scott Armstrong and Amélie Loher. All rights reserved.
-- Released under Apache 2.0 license as described in the file LICENSE.
module

public import RothschildStein.G2.ControlGaugeConstruction

set_option autoImplicit false
set_option relaxedAutoImplicit false
set_option backward.isDefEq.respectTransparency false
@[expose] public section
noncomputable section
open Set
open scoped ENNReal
namespace RothschildStein.G2

/-- Inversion symmetry of the actual control gauge follows
from left invariance and control-distance symmetry (BB (3.35), p. 126). -/
theorem controlDistanceGauge_inv_eq {N m : ℕ} (G : HomogeneousGroup N)
    (w : Fin m → ℕ+) (X : Fin m → (Fin N → ℝ) → (Fin N → ℝ))
    (hleft : ∀ i, IsLeftInvariantField G (X i)) (x : Fin N → ℝ) :
    controlDistanceGauge w X (G.inv x) = controlDistanceGauge w X x := by
  have he := controlDistance_leftInvariant G w X hleft x (G.inv x) 0
  rw [mul_inv G,mul_zero G] at he
  unfold controlDistanceGauge
  rw [← he,G1.controlDistance_symm univ w X 0 x]

/-- The exact triangle constant is
one. The correct multiplication order gives the triangle bound
(BB (3.34), p. 126). -/
theorem controlDistanceGauge_mul_le_of_finite_distance {N m : ℕ}
    (G : HomogeneousGroup N) (w : Fin m → ℕ+)
    (X : Fin m → (Fin N → ℝ) → (Fin N → ℝ))
    (hleft : ∀ i, IsLeftInvariantField G (X i))
    (hfinite : ∀ x y, controlDistance univ w X x y ≠ ∞) (x y : Fin N → ℝ) :
    controlDistanceGauge w X (G.mul x y) ≤ controlDistanceGauge w X x + controlDistanceGauge w X y := by
  have he := controlDistance_leftInvariant G w X hleft x y 0
  rw [mul_zero G] at he
  have ht := G1.controlDistance_triangle univ w X (G.mul x y) x 0
  rw [he] at ht
  have hr := ENNReal.toReal_mono (ENNReal.add_ne_top.mpr ⟨hfinite y 0,hfinite x 0⟩) ht
  rw [ENNReal.toReal_add (hfinite y 0) (hfinite x 0)] at hr
  simpa only [controlDistanceGauge,add_comm] using hr

/-- The constructed control norm
has c=1 and exactly the control gauge as its function. No norm package,
Chow-finiteness conclusion or topology equality is assumed
(BB Thm 3.54, pp. 125–127; weighted proof p. 140). -/
def controlNorm_of_local_comparison {N m s : ℕ} (G : HomogeneousGroup N)
    (w : Fin m → ℕ+) (X : Fin m → (Fin N → ℝ) → (Fin N → ℝ))
    (hX : ∀ i, Continuous (X i)) (hleft : ∀ i, IsLeftInvariantField G (X i))
    (hhom : ∀ i, IsHomogeneousField G (X i) (w i : ℕ))
    (hs : 0 < s) (hcomparison : G1.LocalControlComparison univ w X s) : HomogeneousNorm G where
  toFun := controlDistanceGauge w X
  gauge := isHomogeneousGauge_controlDistance_of_local_comparison G w X hX hhom hs hcomparison
  c := 1
  one_le_c := le_rfl
  inv_le x := by
    rw [one_mul,controlDistanceGauge_inv_eq G w X hleft]
  mul_le x y := by
    rw [one_mul]
    exact controlDistanceGauge_mul_le_of_finite_distance G w X hleft
      (controlDistance_group_ne_top_of_local_comparison w X hs hcomparison) x y

/-- The full shared control-norm
conclusion is assembled from the actual weighted control distance
(BB Thm 3.54, pp. 125–127). -/
def controlNormConclusion_of_local_comparison {N m s : ℕ} (G : HomogeneousGroup N)
    (w : Fin m → ℕ+) (X : Fin m → (Fin N → ℝ) → (Fin N → ℝ))
    (hX : ∀ i, Continuous (X i)) (hleft : ∀ i, IsLeftInvariantField G (X i))
    (hhom : ∀ i, IsHomogeneousField G (X i) (w i : ℕ))
    (hs : 0 < s) (hcomparison : G1.LocalControlComparison univ w X s) :
    ControlNormConclusion G w X where
  norm := controlNorm_of_local_comparison G w X hX hleft hhom hs hcomparison
  constant_one := rfl
  symmetric := controlDistanceGauge_inv_eq G w X hleft
  distance_eq x y := by
    change controlDistance univ w X x y =
      ENNReal.ofReal (controlDistanceGauge w X (G.mul (G.inv y) x))
    rw [controlDistance_gauge G w X hleft]
    exact (ENNReal.ofReal_toReal
      (controlDistance_group_ne_top_of_local_comparison w X hs hcomparison (G.mul (G.inv y) x) 0)).symm

end RothschildStein.G2

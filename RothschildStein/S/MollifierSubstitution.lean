-- Copyright (c) 2026 Scott Armstrong and Amélie Loher. All rights reserved.
-- Released under Apache 2.0 license as described in the file LICENSE.
module

public import RothschildStein.S.MollifierConvergence
public import RothschildStein.G2.MollifierSubstitution
public import Mathlib.MeasureTheory.Group.Integral

set_option autoImplicit false
set_option relaxedAutoImplicit false
@[expose] public section
noncomputable section
open MeasureTheory
namespace RothschildStein.S
variable {n : ℕ}

/-- Ordinary convolution has the fixed-kernel minus-sign
formula (BB Lemma 2.8, p. 72; change of variables). -/
theorem euclideanRegularize_eq_integral_sub (hn : 0 < n)
    (f : (Fin n → ℝ) → ℝ) {ε : ℝ} (hε : 0 < ε) (x : Fin n → ℝ) :
    euclideanRegularize n f ε x = ∫ y, euclideanJ n y * f (x-ε • y) := by
  rw [← additiveRegularize_eq hn]
  rw [RothschildStein.G2.groupRegularize_eq_integral _ _ _ hε]
  apply integral_congr_ae
  exact Filter.Eventually.of_forall fun y => by
    change euclideanJ n y * f ((additiveCoordinateGroup hn).mul
      ((additiveCoordinateGroup hn).inv ((additiveCoordinateGroup hn).dilate ε y)) x) =
      euclideanJ n y * f (x-ε • y)
    rw [additiveCoordinateGroup_dilate,additiveCoordinateGroup_inv,
      additiveCoordinateGroup_mul]
    congr 2
    abel

/-- Evenness gives the plus-sign formula for the Friedrichs kernel (BB (2.6)–(2.8), p. 75). -/
theorem euclideanRegularize_eq_integral_add (hn : 0 < n)
    (f : (Fin n → ℝ) → ℝ) {ε : ℝ} (hε : 0 < ε) (x : Fin n → ℝ) :
    euclideanRegularize n f ε x = ∫ y, euclideanJ n y * f (x+ε • y) := by
  rw [euclideanRegularize_eq_integral_sub hn f hε x]
  rw [← integral_neg_eq_self (fun y : Fin n → ℝ => euclideanJ n y * f (x-ε • y))]
  apply integral_congr_ae
  exact Filter.Eventually.of_forall fun y => by
    change euclideanJ n (-y) * f (x-ε • (-y)) = euclideanJ n y * f (x+ε • y)
    rw [euclideanJ_even,smul_neg,sub_neg_eq_add]

end RothschildStein.S

-- Copyright (c) 2026 Scott Armstrong and Amélie Loher. All rights reserved.
-- Released under Apache 2.0 license as described in the file LICENSE.
module

public import RothschildStein.S.AdditiveGroup
public import RothschildStein.G2.DilationMeasure

set_option autoImplicit false
set_option relaxedAutoImplicit false
@[expose] public section
noncomputable section
open MeasureTheory
namespace RothschildStein.S
variable {n : ℕ}

/-- Positive scalar dilation transforms coordinate Lebesgue
integrals by ε^{-n}, including coordinate dimension zero
(BB (2.8),(2.11), pp. 75–78; change-of-variables). -/
theorem integral_coordinate_smul {ε : ℝ} (hε : 0 < ε)
    (f : (Fin n → ℝ) → ℝ) :
    (∫ y, f (ε • y)) = (ε^n)⁻¹ * ∫ y, f y := by
  by_cases hn : n = 0
  · subst n
    have he : (fun y : Fin 0 → ℝ => f (ε • y)) = f :=
      funext fun y => congrArg f (Subsingleton.elim _ _)
    rw [he]
    simp only [pow_zero,inv_one,one_mul]
  · have H := RothschildStein.G2.integral_dilate
      (additiveCoordinateGroup (Nat.pos_of_ne_zero hn)) hε f
    have hd : (additiveCoordinateGroup (Nat.pos_of_ne_zero hn)).homogeneousDimension = n := by
      simp [HomogeneousGroup.homogeneousDimension,additiveCoordinateGroup]
    simpa only [additiveCoordinateGroup_dilate,hd,smul_eq_mul] using H

end RothschildStein.S

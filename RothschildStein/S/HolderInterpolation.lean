-- Copyright (c) 2026 Scott Armstrong and Amélie Loher. All rights reserved.
-- Released under Apache 2.0 license as described in the file LICENSE.
module

public import RothschildStein.S.HolderBounds

set_option autoImplicit false
set_option relaxedAutoImplicit false
@[expose] public section
noncomputable section
open Set
open scoped ENNReal
namespace RothschildStein.S
variable {n : ℕ}

/-- Combining a bounded increment estimate and a
Lipschitz increment estimate gives the exact interpolated Hölder
constant, including exponent one and zero bounds
(BB (2.15), p. 81; interpolation). -/
theorem holderSeminorm_le_interpolated_increment_bounds
    (d : (Fin n → ℝ) → (Fin n → ℝ) → ℝ≥0∞)
    (V : Set (Fin n → ℝ)) (f : (Fin n → ℝ) → ℝ)
    {α : ℝ} (hα : 0 < α) (hα1 : α ≤ 1)
    (A B : ℝ≥0∞) (hA : A < ⊤) (hB : B < ⊤)
    (hb : ∀ x ∈ V,∀ y ∈ V,d x y < ⊤ → ENNReal.ofReal |f x-f y| ≤ A)
    (hl : ∀ x ∈ V,∀ y ∈ V,d x y < ⊤ → ENNReal.ofReal |f x-f y| ≤ B*d x y) :
    holderSeminorm d α V f ≤ A^(1-α)*B^α := by
  have ha : 0 ≤ 1-α := sub_nonneg.mpr hα1
  apply holderSeminorm_le_of_bound
  · exact ENNReal.mul_lt_top (ENNReal.rpow_lt_top_of_nonneg ha hA.ne)
      (ENNReal.rpow_lt_top_of_nonneg hα.le hB.ne)
  · intro x hx y hy hd
    let v := ENNReal.ofReal |f x-f y|
    calc
      v = v^(1-α)*v^α := by
        rw [← ENNReal.rpow_add_of_nonneg (1-α) α ha hα.le]
        simp only [sub_add_cancel,ENNReal.rpow_one]
      _ ≤ A^(1-α)*(B*d x y)^α :=
        mul_le_mul' (ENNReal.rpow_le_rpow (hb x hx y hy hd) ha)
          (ENNReal.rpow_le_rpow (hl x hx y hy hd) hα.le)
      _ = _ := by rw [ENNReal.mul_rpow_of_nonneg _ _ hα.le,mul_assoc]

end RothschildStein.S

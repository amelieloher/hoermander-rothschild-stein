-- Copyright (c) 2026 Scott Armstrong and Amélie Loher. All rights reserved.
-- Released under Apache 2.0 license as described in the file LICENSE.
module

public import RothschildStein.S.HolderInterpolation
public import RothschildStein.S.DistanceGeometry

set_option autoImplicit false
set_option relaxedAutoImplicit false
set_option backward.isDefEq.respectTransparency false
@[expose] public section
noncomputable section
open Set
open scoped ENNReal
namespace RothschildStein.S
variable {n : ℕ}

/-- A bounded Euclidean Lipschitz function obeys the exact
BB Hölder seminorm bound on any comparison patch, with the original
ambient distance (BB (2.15), p. 81; interpolation with the local distance comparison). -/
theorem holderSeminorm_le_of_lipschitz_comparison
    (d : (Fin n → ℝ) → (Fin n → ℝ) → ℝ≥0∞)
    (V : Set (Fin n → ℝ)) (f : (Fin n → ℝ) → ℝ)
    {κ Λ α : ℝ} (hκ : DistanceComparison d V κ)
    (hΛ : 0 ≤ Λ) (hα : 0 < α) (hα1 : α ≤ 1)
    (M : ℝ≥0∞) (hM : M < ⊤) (hb : ∀ x ∈ V,ENNReal.ofReal |f x| ≤ M)
    (hl : ∀ x ∈ V,∀ y ∈ V,|f x-f y| ≤ Λ*‖x-y‖) :
    holderSeminorm d α V f ≤ (2*M)^(1-α)*(ENNReal.ofReal (κ*Λ))^α := by
  apply holderSeminorm_le_interpolated_increment_bounds d V f hα hα1 (2*M)
    (ENNReal.ofReal (κ*Λ)) (ENNReal.mul_lt_top (by norm_num) hM) ENNReal.ofReal_lt_top
  · intro x hx y hy _
    calc
      _ ≤ ENNReal.ofReal (|f x|+|f y|) := ENNReal.ofReal_le_ofReal (by
        simpa only [sub_eq_add_neg,abs_neg] using! abs_add_le (f x) (-f y))
      _ = ENNReal.ofReal |f x|+ENNReal.ofReal |f y| := ENNReal.ofReal_add (abs_nonneg _) (abs_nonneg _)
      _ ≤ M+M := add_le_add (hb x hx) (hb y hy)
      _ = 2*M := by ring
  · intro x hx y hy _
    calc
      _ ≤ ENNReal.ofReal (Λ*‖x-y‖) := ENNReal.ofReal_le_ofReal (hl x hx y hy)
      _ = ENNReal.ofReal Λ*ENNReal.ofReal ‖x-y‖ := ENNReal.ofReal_mul hΛ
      _ ≤ ENNReal.ofReal Λ*(ENNReal.ofReal κ*d x y) := mul_le_mul_right (hκ.2 x hx y hy) _
      _ = ENNReal.ofReal (κ*Λ)*d x y := by rw [ENNReal.ofReal_mul hκ.1.le]; ring

end RothschildStein.S

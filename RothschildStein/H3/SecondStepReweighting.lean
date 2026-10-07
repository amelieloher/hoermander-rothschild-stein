-- Copyright (c) 2026 Scott Armstrong and Amélie Loher. All rights reserved.
-- Released under Apache 2.0 license as described in the file LICENSE.
module

public import RothschildStein.H3.PhiAbsorption
public import Mathlib.Tactic.FieldSimp

set_option autoImplicit false
set_option relaxedAutoImplicit false
@[expose] public section
noncomputable section
namespace RothschildStein.H3
open Set

/-- The midpoint cutoff step has the exact weighted Phi
coefficients 8aC and 4bC, and the source coefficient Cr squared / 4. -/
theorem second_step_reweighted {r σ C a b F U n₁ n₂ P₀ P₁ : ℝ}
    (hr : 0 < r) (hσ : σ ∈ Ioo (1/2 : ℝ) 1)
    (hC : 0 ≤ C) (ha : 0 ≤ a) (hb : 0 ≤ b) (hF : 0 ≤ F)
    (hstep : n₂ ≤ C * (F + b / (((1-σ)*r)/2)^2 * U +
      2*a / (((1-σ)*r)/2) * n₁))
    (hP₀ : U ≤ P₀) (hP₁ : (((1-σ)*r)/2) * n₁ ≤ P₁) :
    ((1-σ)*r)^2 * n₂ ≤ C*r^2/4*F + 8*a*C*P₁ + 4*b*C*P₀ := by
  let w := (1-σ)*r
  have hw : 0 < w := mul_pos (sub_pos.mpr hσ.2) hr
  have hwr : w ≤ r/2 := by
    dsimp only [w]
    nlinarith [hσ.1]
  have hwsq : w^2 ≤ r^2/4 := by nlinarith
  have he : w^2 * (C * (F + b/(w/2)^2*U + 2*a/(w/2)*n₁)) =
      C*w^2*F + 8*a*C*(w/2*n₁) + 4*b*C*U := by
    field_simp [ne_of_gt hw]
    ring
  have hfirst : C*w^2*F ≤ C*(r^2/4)*F := by gcongr
  have hcross : 8*a*C*(w/2*n₁) ≤ 8*a*C*P₁ :=
    mul_le_mul_of_nonneg_left hP₁ (by positivity)
  have hzero : 4*b*C*U ≤ 4*b*C*P₀ :=
    mul_le_mul_of_nonneg_left hP₀ (by positivity)
  calc
    w^2*n₂ ≤ w^2*(C*(F+b/(w/2)^2*U+2*a/(w/2)*n₁)) :=
      mul_le_mul_of_nonneg_left hstep (sq_nonneg w)
    _ = C*w^2*F + 8*a*C*(w/2*n₁) + 4*b*C*U := he
    _ ≤ C*(r^2/4)*F + 8*a*C*P₁ + 4*b*C*P₀ :=
      add_le_add (add_le_add hfirst hcross) hzero
    _ = C*r^2/4*F + 8*a*C*P₁ + 4*b*C*P₀ := by ring

end RothschildStein.H3

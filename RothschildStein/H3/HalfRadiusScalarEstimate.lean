-- Copyright (c) 2026 Scott Armstrong and Amélie Loher. All rights reserved.
-- Released under Apache 2.0 license as described in the file LICENSE.
module

public import RothschildStein.H3.LocalEstimateAbsorption

set_option autoImplicit false
set_option relaxedAutoImplicit false
@[expose] public section
namespace RothschildStein.H3

/-- The exact half-radius weights convert absorbed Phi bounds to the
scale-invariant sum, with one positive constant independent of the radius. -/
theorem halfRadius_scalar_estimate {r A B δ cE F U P₁ P₂ N₁ N₂ Uhalf : ℝ}
    (hr : 0 < r) (hA : 0 ≤ A) (hB : 0 ≤ B) (hδ : 0 < δ)
    (hcE : 0 ≤ cE) (hF : 0 ≤ F) (hU : 0 ≤ U)
    (h₂ : P₂ ≤ A*r^2*F+B*U)
    (h₁ : P₁ ≤ δ*(A*r^2*F+B*U)+cE/δ*U)
    (hhalf₂ : (r/2)^2*N₂ ≤ P₂)
    (hhalf₁ : (r/2)*N₁ ≤ P₁) (hhalf₀ : Uhalf ≤ U) :
    let K := 1+(4+2*δ)*A+(4+2*δ)*B+2*cE/δ
    0 < K ∧ N₂+r⁻¹*N₁+r⁻¹^2*Uhalf ≤ K*(F+r⁻¹^2*U) := by
  dsimp only
  have hi : 0 ≤ r⁻¹^2 := sq_nonneg _
  have hs₂ : N₂ ≤ 4*A*F+4*B*(r⁻¹^2*U) := by
    have hh := mul_le_mul_of_nonneg_left (hhalf₂.trans h₂) (show 0 ≤ 4/r^2 by positivity)
    convert hh using 1 <;> field_simp [ne_of_gt hr]
    ring
  have hs₁ : r⁻¹*N₁ ≤ 2*δ*A*F+(2*δ*B+2*cE/δ)*(r⁻¹^2*U) := by
    have hh := mul_le_mul_of_nonneg_left (hhalf₁.trans h₁) (show 0 ≤ 2/r^2 by positivity)
    convert hh using 1 <;> field_simp [ne_of_gt hr]
    ring
  have hs₀ := mul_le_mul_of_nonneg_left hhalf₀ hi
  have hcoefA : 0 ≤ (4+2*δ)*A := by positivity
  have hcoefB : 0 ≤ (4+2*δ)*B := by positivity
  have hcoefE : 0 ≤ 2*cE/δ := by positivity
  refine ⟨by positivity, ?_⟩
  have hUF : 0 ≤ r⁻¹^2*U := mul_nonneg hi hU
  nlinarith [mul_nonneg hcoefA hUF, mul_nonneg hcoefB hF,
    mul_nonneg hcoefE hF]

end RothschildStein.H3

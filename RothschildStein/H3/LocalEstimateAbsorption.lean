-- Copyright (c) 2026 Scott Armstrong and Amélie Loher. All rights reserved.
-- Released under Apache 2.0 license as described in the file LICENSE.
module

public import RothschildStein.H3.CutoffInterpolation

set_option autoImplicit false
set_option relaxedAutoImplicit false
@[expose] public section
noncomputable section
namespace RothschildStein.H3

/-- Absorb the first derivative term using the normalized second-order
estimate. The factor two from the product expansion is retained in a. -/
theorem localEstimate_scalar_absorption {P₀ P₁ P₂ F r C a b cE δ : ℝ}
    (hP₂ : 0 ≤ P₂) (hsmall : a * δ ≤ 1 / 2)
    (ha : 0 ≤ a)
    (hsecond : P₂ ≤ C * r^2 / 4 * F + a * P₁ + b * P₀)
    (hfirst : P₁ ≤ δ * P₂ + cE / δ * P₀) :
    P₂ ≤ C * r^2 / 2 * F + 2 * (b + a * cE / δ) * P₀ := by
  have hscaled := mul_le_mul_of_nonneg_left hfirst ha
  have hhalf : a * δ * P₂ ≤ P₂ / 2 := by nlinarith
  have heq : a * (δ * P₂ + cE / δ * P₀) =
      a * δ * P₂ + (a * cE / δ) * P₀ := by ring
  rw [heq] at hscaled
  nlinarith only [hsecond, hscaled, hhalf]

/-- A positive admissible interpolation parameter depending only
on the analytic constants, including the case a=0. -/
theorem exists_localEstimate_absorption_parameter {a δE : ℝ}
    (ha : 0 ≤ a) (hδE : 0 < δE) :
    ∃ δ : ℝ, 0 < δ ∧ δ ≤ δE ∧ a * δ ≤ 1 / 2 := by
  refine ⟨min δE (1 / (2 * (a + 1))), by positivity, min_le_left _ _, ?_⟩
  have hd : min δE (1 / (2 * (a + 1))) ≤ 1 / (2 * (a + 1)) := min_le_right _ _
  have hpos : 0 < 2 * (a + 1) := by positivity
  have hm := (le_div_iff₀ hpos).mp hd
  have hδ : 0 ≤ min δE (1 / (2 * (a + 1))) := by positivity
  nlinarith

end RothschildStein.H3

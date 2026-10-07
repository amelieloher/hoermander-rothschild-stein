-- Copyright (c) 2026 Scott Armstrong and Amélie Loher. All rights reserved.
-- Released under Apache 2.0 license as described in the file LICENSE.
module

public import Mathlib.Analysis.SpecialFunctions.Pow.Real
public import Mathlib.Tactic

set_option autoImplicit false
set_option relaxedAutoImplicit false
@[expose] public section
noncomputable section
namespace RothschildStein.H3

/-- The scalar product estimate for Case I keeps the cutoff contribution
and the homogeneous increment contribution linear in the same seminorm. -/
theorem cutoff_far_difference_bound
    {b₀ b₁ t₀ t₁ ρ δ R L I Λ γ : ℝ}
    (hρ : 0 < ρ) (hδ : 0 ≤ δ) (hR : 0 ≤ R) (hL : 0 ≤ L)
    (hI : 0 ≤ I) (hΛ : 0 ≤ Λ)
    (hb₀ : 0 ≤ b₀ ∧ b₀ ≤ 1) (hb₁ : 0 ≤ b₁ ∧ b₁ ≤ 1)
    (hcut : |b₀ - b₁| ≤ L * δ)
    (hinc : |t₀ - t₁| ≤ I * Λ * δ * ρ ^ (γ - 1))
    (hsize : |t₁| ≤ Λ * (2 : ℝ) ^ (-γ) * ρ ^ γ)
    (hactive : b₀ ≠ 0 ∨ b₁ ≠ 0 → ρ ≤ 2 * R) :
    |b₀ * t₀ - b₁ * t₁| ≤
      (I + (2 : ℝ) ^ (-γ) * (2 * R * L)) * Λ * δ * ρ ^ (γ - 1) := by
  by_cases hz : b₀ = 0 ∧ b₁ = 0
  · rw [hz.1, hz.2, zero_mul, zero_mul, sub_self, abs_zero]
    positivity
  have hρR : ρ ≤ 2 * R := hactive (by tauto)
  have hp : 0 ≤ ρ ^ (γ - 1) := Real.rpow_nonneg hρ.le _
  have htwo : 0 ≤ (2 : ℝ) ^ (-γ) := Real.rpow_nonneg (by norm_num) _
  have hsplit : b₀ * t₀ - b₁ * t₁ = b₀ * (t₀ - t₁) + (b₀ - b₁) * t₁ := by ring
  have hfirst : |b₀ * (t₀ - t₁)| ≤ I * Λ * δ * ρ ^ (γ - 1) := by
    rw [abs_mul, abs_of_nonneg hb₀.1]
    exact (mul_le_mul_of_nonneg_right hb₀.2 (abs_nonneg _)).trans
      (by simpa only [one_mul] using hinc)
  have hpow : ρ ^ γ = ρ * ρ ^ (γ - 1) := by
    rw [Real.rpow_sub_one hρ.ne']
    field_simp
  have hsecond : |(b₀ - b₁) * t₁| ≤
      ((2 : ℝ) ^ (-γ) * (2 * R * L)) * Λ * δ * ρ ^ (γ - 1) := by
    rw [abs_mul]
    calc
      _ ≤ (L * δ) * (Λ * (2 : ℝ) ^ (-γ) * ρ ^ γ) :=
        mul_le_mul hcut hsize (abs_nonneg _) (mul_nonneg hL hδ)
      _ = ((2 : ℝ) ^ (-γ) * L * ρ) * (Λ * δ * ρ ^ (γ - 1)) := by
        rw [hpow]
        ring
      _ ≤ ((2 : ℝ) ^ (-γ) * L * (2 * R)) * (Λ * δ * ρ ^ (γ - 1)) :=
        mul_le_mul_of_nonneg_right
          (mul_le_mul_of_nonneg_left hρR (mul_nonneg htwo hL))
          (mul_nonneg (mul_nonneg hΛ hδ) hp)
      _ = _ := by ring
  rw [hsplit]
  exact (abs_add_le _ _).trans ((add_le_add hfirst hsecond).trans_eq (by ring))

end RothschildStein.H3

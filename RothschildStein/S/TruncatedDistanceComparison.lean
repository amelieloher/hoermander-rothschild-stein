-- Copyright (c) 2026 Scott Armstrong and Amélie Loher. All rights reserved.
-- Released under Apache 2.0 license as described in the file LICENSE.
module

public import Mathlib.Analysis.SpecialFunctions.Pow.Real

set_option autoImplicit false
set_option relaxedAutoImplicit false
@[expose] public section
noncomputable section
namespace RothschildStein.S

/-- A local truncated distance lower bound yields one
linear comparison constant on a bounded patch (BB Prop 1.42, pp. 23–24;
Thm 1.53, (1.45), p. 35). -/
theorem exists_truncated_distance_comparison_constant
    {B ρ D : ℝ} (hB : 0 < B) (hρ : 0 < ρ) (_hD : 0 ≤ D) :
    ∃ κ : ℝ,0 < κ ∧ ∀ a : ℝ,0 ≤ a → a ≤ D → a ≤ κ*min ρ (a/B) := by
  let κ := max B (D/ρ)+1
  have hκB : B ≤ κ := by dsimp [κ]; linarith [le_max_left B (D/ρ)]
  have hκD : D/ρ ≤ κ := by dsimp [κ]; linarith [le_max_right B (D/ρ)]
  refine ⟨κ,hB.trans_le hκB,?_⟩
  intro a ha haD
  by_cases h : a/B ≤ ρ
  · rw [min_eq_right h]
    have hm := mul_le_mul_of_nonneg_right hκB (div_nonneg ha hB.le)
    have he : B*(a/B) = a := by field_simp [hB.ne']
    rw [he] at hm
    exact hm
  · rw [min_eq_left (le_of_not_ge h)]
    exact haD.trans ((div_le_iff₀ hρ).mp hκD)

end RothschildStein.S

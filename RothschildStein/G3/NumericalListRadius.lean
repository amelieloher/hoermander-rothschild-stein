-- Copyright (c) 2026 Scott Armstrong and Amélie Loher. All rights reserved.
-- Released under Apache 2.0 license as described in the file LICENSE.
module
public import Mathlib.Analysis.Normed.Module.Basic
@[expose] public section
set_option autoImplicit false
set_option relaxedAutoImplicit false
noncomputable section
namespace RothschildStein.G3

/-- One radius controls coefficient smallness and every bounded-length prefix. -/
theorem exists_numerical_list_radius {σ ρ C R : ℝ} (hσ : 0 < σ) (hρ : 0 < ρ)
    (hC : 0 ≤ C) (hR : 0 ≤ R) (L : ℕ) :
    ∃ η : ℝ, 0 < η ∧ η ≤ 1 ∧ ∀ t : ℝ, |t| < η →
      |t| *R < σ ∧ (L : ℝ)*C*|t| *R < ρ := by
  let A : ℝ := (L+1)*(C+1)*(R+1)
  have hA : 0 < A := by dsimp [A]; positivity
  let η := min 1 (min (σ/(2*(R+1))) (ρ/(2*A)))
  have hη : 0 < η := lt_min zero_lt_one (lt_min (by positivity) (by positivity))
  refine ⟨η,hη,min_le_left _ _,?_⟩
  intro t ht
  have hc : |t| *(2*(R+1)) < σ :=
    (lt_div_iff₀ (by positivity)).mp (ht.trans_le ((min_le_right _ _).trans (min_le_left _ _)))
  have hb : |t| *(2*A) < ρ :=
    (lt_div_iff₀ (by positivity)).mp (ht.trans_le ((min_le_right _ _).trans (min_le_right _ _)))
  have hprod : (L : ℝ)*C*R ≤ A := by
    dsimp [A]
    apply mul_le_mul
    · apply mul_le_mul
      · linarith
      · linarith
      · exact hC
      · positivity
    · linarith
    · exact hR
    · positivity
  have hs : (L : ℝ)*C*|t| *R ≤ |t| *A := by
    calc
      (L : ℝ)*C*|t| *R = |t| *((L : ℝ)*C*R) := by ring
      _ ≤ |t| *A := mul_le_mul_of_nonneg_left hprod (abs_nonneg t)
  constructor
  · nlinarith [abs_nonneg t]
  · nlinarith [mul_nonneg (abs_nonneg t) hA.le]
end RothschildStein.G3

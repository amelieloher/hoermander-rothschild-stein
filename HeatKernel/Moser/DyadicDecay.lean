-- Copyright (c) 2026 Scott Armstrong and Amélie Loher. All rights reserved.
-- Released under Apache 2.0 license as described in the file LICENSE.
module

public import Mathlib

/-! # Power decay from dyadic oscillation estimates

Geometric contraction at half radii gives a power modulus at every intermediate radius.
The exponent can be chosen strictly between zero and one.
-/

@[expose] public section

open Set

namespace HeatKernel

/-- Every strict contraction is bounded by a dyadic power with exponent in `(0, 1)`. -/
theorem exists_dyadic_holder_exponent {θ : ℝ} (hθ : θ ∈ Ioo (0 : ℝ) 1) :
    ∃ α : ℝ, α ∈ Ioo (0 : ℝ) 1 ∧ θ ≤ (1 / 2 : ℝ) ^ α := by
  let α := min (Real.logb (1 / 2) θ) (1 / 2)
  have hp : 0 < Real.logb (1 / 2) θ :=
    Real.logb_pos_of_base_lt_one (by norm_num) (by norm_num) hθ.1 hθ.2
  refine ⟨α, ⟨lt_min hp (by norm_num), (min_le_right _ _).trans_lt (by norm_num)⟩, ?_⟩
  exact (Real.le_logb_iff_rpow_le_of_base_lt_one
    (by norm_num : (0 : ℝ) < 1 / 2) (by norm_num : (1 / 2 : ℝ) < 1) hθ.1).mp
    (min_le_left _ _)

/-- Iterating a half-radius inequality gives its geometric bound at every dyadic radius. -/
theorem le_pow_mul_of_half_radius_decay {ω : ℝ → ℝ} {R θ : ℝ}
    (hR : 0 < R) (hθ : 0 ≤ θ)
    (hstep : ∀ r : ℝ, 0 < r → r ≤ R → ω (r / 2) ≤ θ * ω r) (n : ℕ) :
    ω (R * (1 / 2 : ℝ) ^ n) ≤ θ ^ n * ω R := by
  induction n with
  | zero => simp
  | succ n hn =>
    have hr : 0 < R * (1 / 2 : ℝ) ^ n := mul_pos hR (pow_pos (by norm_num) _)
    have hrR : R * (1 / 2 : ℝ) ^ n ≤ R := by
      exact mul_le_of_le_one_right hR.le (pow_le_one₀ (by norm_num) (by norm_num))
    have he : R * (1 / 2 : ℝ) ^ (n + 1) = (R * (1 / 2 : ℝ) ^ n) / 2 := by
      rw [pow_succ]
      ring
    rw [he]
    calc
      ω ((R * (1 / 2 : ℝ) ^ n) / 2) ≤ θ * ω (R * (1 / 2 : ℝ) ^ n) := hstep _ hr hrR
      _ ≤ θ * (θ ^ n * ω R) := mul_le_mul_of_nonneg_left hn hθ
      _ = θ ^ (n + 1) * ω R := by rw [pow_succ]; ring

end HeatKernel

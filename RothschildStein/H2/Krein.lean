-- Copyright (c) 2026 Scott Armstrong and Amélie Loher. All rights reserved.
-- Released under Apache 2.0 license as described in the file LICENSE.
module

public import RothschildStein.H2.KreinSymmetric

set_option autoImplicit false
set_option relaxedAutoImplicit false

@[expose] public section
noncomputable section

namespace RothschildStein.H2
variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℝ H]

/-- Krein's bound for one member of an adjoint pair on a dominating
seminorm space. Completeness and density are unnecessary for this bound.
BB Theorem 7.20, pp. 309–310. -/
theorem krein_norm_bound (N : Seminorm ℝ H) (T T' : H →ₗ[ℝ] H)
    {k a b : ℝ} (hk : 0 ≤ k) (ha : 0 ≤ a) (hb : 0 ≤ b)
    (hdom : ∀ y, ‖y‖ ≤ k * N y)
    (hT : ∀ y, N (T y) ≤ a * N y) (hT' : ∀ y, N (T' y) ≤ b * N y)
    (hadj : ∀ x y, inner ℝ (T x) y = inner ℝ x (T' y)) (y : H) :
    ‖T y‖ ≤ Real.sqrt (a * b) * ‖y‖ := by
  let S := T' * T
  have hS : S.IsSymmetric := by
    intro x y
    change inner ℝ (T' (T x)) y = inner ℝ x (T' (T y))
    calc
      _ = inner ℝ y (T' (T x)) := real_inner_comm _ _
      _ = inner ℝ (T y) (T x) := (hadj y (T x)).symm
      _ = inner ℝ (T x) (T y) := real_inner_comm _ _
      _ = _ := hadj x (T y)
  have hbS : ∀ y, N (S y) ≤ (a * b) * N y := by
    intro y
    exact (hT' (T y)).trans (by
      have he := mul_le_mul_of_nonneg_left (hT y) hb
      convert he using 1
      ring)
  have hnormS := symmetric_norm_bound N S hS hk (mul_nonneg ha hb) hdom hbS y
  have hsq : ‖T y‖ ^ 2 ≤ ‖y‖ * ‖S y‖ := by
    rw [← real_inner_self_eq_norm_sq, hadj]
    exact real_inner_le_norm _ _
  have hsq' : ‖T y‖ ^ 2 ≤ (a * b) * ‖y‖ ^ 2 := by
    have he := mul_le_mul_of_nonneg_left hnormS (norm_nonneg y)
    nlinarith
  have hsqrt := Real.sq_sqrt (mul_nonneg ha hb)
  have hsqrt₀ := Real.sqrt_nonneg (a * b)
  apply (sq_le_sq₀ (norm_nonneg _) (mul_nonneg hsqrt₀ (norm_nonneg y))).mp
  rw [mul_pow, hsqrt]
  exact hsq'

end RothschildStein.H2

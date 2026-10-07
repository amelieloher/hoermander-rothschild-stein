-- Copyright (c) 2026 Scott Armstrong and Amélie Loher. All rights reserved.
-- Released under Apache 2.0 license as described in the file LICENSE.
module
public import RothschildStein.G3.DifferentialPolynomialBounds
@[expose] public section
noncomputable section
open Set TopologicalSpace
open scoped BigOperators
namespace RothschildStein.G3

/-- A polynomial supported at weight at least k has a uniform
small-parameter factor of order k (BB pp. 412–420). This assertion concerns
the finite polynomial itself, before any asymptotic notation is used. -/
theorem weighted_polynomial_tail_bound {a s k : ℕ} {p : Fin a → ℕ+}
    (A : WordCoefficients a s p) (b : BoundedWord a s p → ℝ)
    (hb : ∀ J, 0 ≤ b J) {δ : ℝ} (hδ : |δ| ≤ 1)
    (hA : ∀ J, wordWeight p J.val < k → A J = 0) :
    (∑ J : BoundedWord a s p, |A J| * (|δ| ^ wordWeight p J.val * b J)) ≤
      |δ| ^ k * ∑ J : BoundedWord a s p, |A J| * b J := by
  classical
  rw [Finset.mul_sum]
  apply Finset.sum_le_sum
  intro J _
  by_cases hJ : wordWeight p J.val < k
  · simp only [hA J hJ, abs_zero, zero_mul, mul_zero, le_refl]
  · calc
      |A J| * (|δ| ^ wordWeight p J.val * b J) ≤
          |A J| * (|δ| ^ k * b J) :=
        mul_le_mul_of_nonneg_left
          (mul_le_mul_of_nonneg_right
            (pow_le_pow_of_le_one (abs_nonneg δ) hδ (by omega)) (hb J)) (abs_nonneg _)
      _ = |δ| ^ k * (|A J| * b J) := by ring

end RothschildStein.G3

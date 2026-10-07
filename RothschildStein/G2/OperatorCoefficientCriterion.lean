-- Copyright (c) 2026 Scott Armstrong and Amélie Loher. All rights reserved.
-- Released under Apache 2.0 license as described in the file LICENSE.
module

public import RothschildStein.G2.PartialDilation
public import RothschildStein.G2.FiniteSymbol

set_option autoImplicit false
set_option relaxedAutoImplicit false
set_option backward.isDefEq.respectTransparency false
@[expose] public section
noncomputable section
open scoped BigOperators
namespace RothschildStein.G2
variable {N : ℕ} (G : HomogeneousGroup N)

/-- Operator homogeneity
is equivalent to the scaled relation for every effective coefficient.
The proof tests on exponentials and uses finite polynomial uniqueness
(BB Definition 3.22 / Proposition 3.23, pp. 106–107). -/
theorem operator_homogeneous_iff_scaled_coefficients
    (P : SmoothDifferentialOperator N) (β : ℝ) :
    P.IsHomogeneous G β ↔ ∀ a ∈ P.indices, ∀ t : ℝ, 0 < t → ∀ x,
      P.coefficient a x * t ^ (∑ j, G.weight j * a j) =
        t ^ β * P.coefficient a (G.dilate t x) := by
  classical
  constructor
  · intro h a ha t ht x
    have he (z : Fin N → ℝ) := h (exponentialTest z) (exponentialTest_smooth z) t ht x
    have hm (z : Fin N → ℝ) :
        (∑ b ∈ P.indices, (P.coefficient b x * t ^ (∑ j, G.weight j * b j)) *
          ∏ j, z j ^ b j) =
        ∑ b ∈ P.indices, (t ^ β * P.coefficient b (G.dilate t x)) * ∏ j, z j ^ b j := by
      specialize he z
      simp only [SmoothDifferentialOperator.apply, euclideanPartial_dilate G _ _
        (exponentialTest_smooth z), euclideanPartial_exponential] at he
      have hl : (∑ b ∈ P.indices, P.coefficient b x *
          (t ^ (∑ j, G.weight j * b j) * ((∏ j, z j ^ b j) *
            exponentialTest z (G.dilate t x)))) =
          (∑ b ∈ P.indices, (P.coefficient b x * t ^ (∑ j, G.weight j * b j)) *
            ∏ j, z j ^ b j) * exponentialTest z (G.dilate t x) := by
        rw [Finset.sum_mul]
        apply Finset.sum_congr rfl
        intro b hb
        ring
      rw [hl, Finset.mul_sum] at he
      have hr : (∑ b ∈ P.indices, t ^ β * (P.coefficient b (G.dilate t x) *
          ((∏ j, z j ^ b j) * exponentialTest z (G.dilate t x)))) =
          (∑ b ∈ P.indices, (t ^ β * P.coefficient b (G.dilate t x)) * ∏ j, z j ^ b j) *
            exponentialTest z (G.dilate t x) := by
        rw [Finset.sum_mul]
        apply Finset.sum_congr rfl
        intro b hb
        ring
      rw [hr] at he
      exact mul_right_cancel₀ (Real.exp_ne_zero _) he
    exact finite_monomials_separate P.indices _ _ hm a ha
  · intro hc f hf t ht x
    simp only [SmoothDifferentialOperator.apply, euclideanPartial_dilate G _ f hf]
    rw [Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro a ha
    rw [← _root_.mul_assoc, hc a ha t ht x]
    ring

/-- For a smooth finite-order operator, homogeneity is equivalent to the scaling law for each coefficient in its finite support (BB pp. 106–107). -/
theorem operator_homogeneous_iff_coefficients
    (P : SmoothDifferentialOperator N) (β : ℝ) :
    P.IsHomogeneous G β ↔ ∀ a ∈ P.indices, ∀ t : ℝ, 0 < t → ∀ x,
      P.coefficient a (G.dilate t x) =
        t ^ ((∑ j, G.weight j * a j : ℕ) - β) * P.coefficient a x := by
  rw [operator_homogeneous_iff_scaled_coefficients G P β]
  have hn (t : ℝ) (ht : 0 < t) : t ^ β ≠ 0 := ne_of_gt (Real.rpow_pos_of_pos ht β)
  constructor
  · intro h a ha t ht x
    apply (mul_left_cancel₀ (hn t ht))
    rw [Real.rpow_sub ht, Real.rpow_natCast]
    have he := h a ha t ht x
    field_simp
    nlinarith [he]
  · intro h a ha t ht x
    rw [h a ha t ht x, Real.rpow_sub ht, Real.rpow_natCast]
    field_simp

end RothschildStein.G2

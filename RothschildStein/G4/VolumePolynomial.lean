-- Copyright (c) 2026 Scott Armstrong and Amélie Loher. All rights reserved.
-- Released under Apache 2.0 license as described in the file LICENSE.
module

public import Mathlib.Analysis.SpecialFunctions.Pow.Real

@[expose] public section
set_option autoImplicit false
set_option relaxedAutoImplicit false
noncomputable section
open Set
open scoped BigOperators

namespace RothschildStein.G4

/-- The finite volume polynomial Λ. The index type is the finite
frame list, lam its determinant coefficients, and w its total weights
(BB equation (9.1), p. 400). -/
def volumePolynomial {ι : Type*} [Fintype ι] (lam : ι → ℝ) (w : ι → ℕ) (r : ℝ) : ℝ :=
  ∑ B, |lam B| * r ^ w B

/-- Every coefficient of Λ is nonnegative (BB (9.1), p. 400). -/
theorem volumePolynomial_nonneg {ι : Type*} [Fintype ι]
    (lam : ι → ℝ) (w : ι → ℕ) {r : ℝ} (hr : 0 ≤ r) : 0 ≤ volumePolynomial lam w r :=
  Finset.sum_nonneg (fun B _ => mul_nonneg (abs_nonneg (lam B)) (pow_nonneg hr (w B)))

/-- A nonzero frame makes Λ strictly positive at every positive
radius (BB (9.1), p. 400). -/
theorem volumePolynomial_pos {ι : Type*} [Fintype ι]
    (lam : ι → ℝ) (w : ι → ℕ) {r : ℝ} (hr : 0 < r) (B : ι) (hB : lam B ≠ 0) :
    0 < volumePolynomial lam w r := by
  exact (mul_pos (abs_pos.mpr hB) (pow_pos hr _)).trans_le
    (Finset.single_le_sum (fun C _ => mul_nonneg (abs_nonneg _) (pow_nonneg hr.le _))
      (Finset.mem_univ B))

/-- Finite weights at most D give the exact fixed-factor polynomial
bound Λ(Ar)≤A^DΛ(r), including radius zero (BB Thm 9.1, p. 400). -/
theorem volumePolynomial_scale_le {ι : Type*} [Fintype ι]
    (lam : ι → ℝ) (w : ι → ℕ) {D : ℕ} (hw : ∀ B, w B ≤ D)
    {A r : ℝ} (hA : 1 ≤ A) (hr : 0 ≤ r) :
    volumePolynomial lam w (A * r) ≤ A ^ D * volumePolynomial lam w r := by
  unfold volumePolynomial
  rw [Finset.mul_sum]
  apply Finset.sum_le_sum
  intro B _
  rw [mul_pow]
  have hpow := pow_le_pow_right₀ hA (hw B)
  have hm := mul_le_mul_of_nonneg_right hpow (mul_nonneg (abs_nonneg (lam B)) (pow_nonneg hr (w B)))
  nlinarith [hm]

/-- A maximizing weighted determinant dominates Λ divided by the
number of frames (BB proof of Thm 9.12, p. 405). -/
theorem volumePolynomial_le_card_mul_of_maximizer {ι : Type*} [Fintype ι]
    (lam : ι → ℝ) (w : ι → ℕ) (r : ℝ) (B : ι)
    (hB : ∀ C, |lam C| * r ^ w C ≤ |lam B| * r ^ w B) :
    volumePolynomial lam w r ≤ Fintype.card ι * (|lam B| * r ^ w B) := by
  simpa only [volumePolynomial, Finset.sum_const, Finset.card_univ, nsmul_eq_mul] using
    Finset.sum_le_sum (s := Finset.univ) (fun C _ => hB C)

/-- If every nonzero frame has common weight Q, Λ factors exactly
as r^Q times the determinant coefficient sum. Freeness is not inferred here
(BB Def 10.36 and Cor 10.37, p. 515). -/
theorem volumePolynomial_eq_commonWeight {ι : Type*} [Fintype ι]
    (lam : ι → ℝ) (w : ι → ℕ) (Q : ℕ) (hweight : ∀ B, lam B ≠ 0 → w B = Q) (r : ℝ) :
    volumePolynomial lam w r = r ^ Q * ∑ B, |lam B| := by
  unfold volumePolynomial
  rw [Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro B _
  by_cases hB : lam B = 0
  · simp only [hB, abs_zero, zero_mul, mul_zero]
  · rw [hweight B hB, mul_comm]

end RothschildStein.G4

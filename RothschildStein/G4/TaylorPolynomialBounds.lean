-- Copyright (c) 2026 Scott Armstrong and Amélie Loher. All rights reserved.
-- Released under Apache 2.0 license as described in the file LICENSE.
module

public import RothschildStein.G4.FlowTaylorRemainder

@[expose] public section
set_option autoImplicit false
set_option relaxedAutoImplicit false
noncomputable section
open Set
open scoped BigOperators

namespace RothschildStein.G4

/-- At time one, the Taylor polynomial minus its constant term
is the exact sum of the positive-order derivatives divided by factorials. -/
theorem taylorWithinEval_one_sub_zero (f : ℝ → ℝ) (m : ℕ) :
    taylorWithinEval f m (Icc 0 1) 0 1 - f 0 =
      ∑ j ∈ Finset.range m, ((j + 1).factorial : ℝ)⁻¹ *
        iteratedDerivWithin (j + 1) f (Icc 0 1) 0 := by
  rw [taylor_within_apply, Finset.sum_range_succ']
  simp only [sub_zero, one_pow, mul_one, smul_eq_mul, Nat.factorial_zero, Nat.cast_one,
    inv_one, one_mul, iteratedDerivWithin_zero]
  ring

/-- The finite Taylor polynomial keeps the exact coefficient
budgets and the relative determinant scale. The polynomial of order zero
has zero deviation. -/
theorem taylorWithinEval_one_deviation_bound (f : ℝ → ℝ) (m : ℕ)
    (c : ℕ → ℝ) {e D : ℝ}
    (hbound : ∀ j ∈ Finset.range m, |iteratedDerivWithin (j + 1) f (Icc 0 1) 0| ≤
      c (j + 1) * e ^ (j + 1) * D) :
    |taylorWithinEval f m (Icc 0 1) 0 1 - f 0| ≤
      (∑ j ∈ Finset.range m, ((j + 1).factorial : ℝ)⁻¹ * c (j + 1) * e ^ (j + 1)) * D := by
  rw [taylorWithinEval_one_sub_zero]
  apply (Finset.abs_sum_le_sum_abs _ _).trans
  rw [Finset.sum_mul]
  apply Finset.sum_le_sum
  intro j hj
  rw [abs_mul, abs_inv, abs_of_nonneg (Nat.cast_nonneg _)]
  exact (mul_le_mul_of_nonneg_left (hbound j hj) (inv_nonneg.mpr (Nat.cast_nonneg _))).trans_eq
    (by ring)

/-- A relative Taylor polynomial error and an absolute remainder
combine using the actual determinant denominator lower bound. -/
theorem relative_taylor_error_bound {f : ℝ → ℝ} {m d : ℕ}
    {e r t Δ A B D : ℝ} (he : 0 ≤ e) (hr : 0 < r) (ht : 0 < t) (hΔ : 0 < Δ)
    (hA : 0 ≤ A) (_hB : 0 ≤ B) (hD : t * Δ * r ^ d ≤ D)
    (hpoly : |taylorWithinEval f m (Icc 0 1) 0 1 - f 0| ≤ B * D)
    (hrem : |f 1 - taylorWithinEval f m (Icc 0 1) 0 1| ≤ A * (e * r) ^ d) :
    |f 1 - f 0| ≤ (B + A * e ^ d / (t * Δ)) * D := by
  have hden : 0 < t * Δ := mul_pos ht hΔ
  have hscaled : A * (e * r) ^ d ≤ (A * e ^ d / (t * Δ)) * D := by
    have hmul := mul_le_mul_of_nonneg_left hD
      (div_nonneg (mul_nonneg hA (pow_nonneg he d)) hden.le)
    calc
      _ = (A * e ^ d / (t * Δ)) * (t * Δ * r ^ d) := by rw [mul_pow]; field_simp [ne_of_gt hden]
      _ ≤ _ := hmul
  calc
    _ ≤ |f 1 - taylorWithinEval f m (Icc 0 1) 0 1| +
        |taylorWithinEval f m (Icc 0 1) 0 1 - f 0| := abs_sub_le _ _ _
    _ ≤ A * (e * r) ^ d + B * D := add_le_add hrem hpoly
    _ ≤ (A * e ^ d / (t * Δ)) * D + B * D := add_le_add hscaled le_rfl
    _ = _ := by ring

end RothschildStein.G4

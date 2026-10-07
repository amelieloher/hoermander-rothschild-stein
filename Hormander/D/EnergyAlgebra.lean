-- Copyright (c) 2026 Scott Armstrong and Amélie Loher. All rights reserved.
-- Released under Apache 2.0 license as described in the file LICENSE.
module

public import Hormander.D.Defs
public import Mathlib.Algebra.Order.BigOperators.Ring.Finset

@[expose] public section

namespace Hormander.D

/-- The diagonal first-order terms are controlled by the complete
two-index energy sum. -/
theorem diagonal_sum_le_sqrt_card_mul_sqrt_full_energy {k : ℕ}
    (z : Fin k → Fin k → ℝ) (hz : ∀ i j, 0 ≤ z i j) :
    (∑ i : Fin k, z i i) ≤
      Real.sqrt (k : ℝ) * Real.sqrt (∑ i : Fin k, ∑ j : Fin k, (z i j) ^ 2) := by
  have hsum_nonneg : 0 ≤ ∑ i : Fin k, z i i :=
    Finset.sum_nonneg fun i _ => hz i i
  have henergy_nonneg : 0 ≤ ∑ i : Fin k, ∑ j : Fin k, (z i j) ^ 2 :=
    Finset.sum_nonneg fun i _ => Finset.sum_nonneg fun j _ => sq_nonneg _
  have hcs : (∑ i : Fin k, z i i) ^ 2 ≤
      (k : ℝ) * ∑ i : Fin k, (z i i) ^ 2 := by
    simpa using Finset.sum_mul_sq_le_sq_mul_sq Finset.univ
      (fun _ : Fin k => (1 : ℝ)) (fun i => z i i)
  have hdiag : (∑ i : Fin k, (z i i) ^ 2) ≤
      ∑ i : Fin k, ∑ j : Fin k, (z i j) ^ 2 := by
    apply Finset.sum_le_sum
    intro i hi
    exact Finset.single_le_sum (fun j _ => sq_nonneg (z i j)) (Finset.mem_univ i)
  have hsq : (∑ i : Fin k, z i i) ^ 2 ≤
      (Real.sqrt (k : ℝ) *
        Real.sqrt (∑ i : Fin k, ∑ j : Fin k, (z i j) ^ 2)) ^ 2 := by
    rw [mul_pow, Real.sq_sqrt (Nat.cast_nonneg k), Real.sq_sqrt henergy_nonneg]
    exact hcs.trans (mul_le_mul_of_nonneg_left hdiag (Nat.cast_nonneg k))
  apply (sq_le_sq₀ hsum_nonneg
    (mul_nonneg (Real.sqrt_nonneg _) (Real.sqrt_nonneg _))).mp
  exact hsq

/-- A first-order energy term is absorbed into the two localized data squares. -/
theorem young_absorb_energy_bound {E A B C : ℝ}
    (hE0 : 0 ≤ E) (_hA0 : 0 ≤ A) (_hB0 : 0 ≤ B) (hC0 : 0 ≤ C)
    (hE : E ≤ C * (A * B + B * Real.sqrt E + B ^ 2)) :
    E ≤ (C ^ 2 + 3 * C) * (A ^ 2 + B ^ 2) := by
  have hroot : (Real.sqrt E) ^ 2 = E := Real.sq_sqrt hE0
  have hAB : 2 * A * B ≤ A ^ 2 + B ^ 2 := by
    nlinarith [sq_nonneg (A - B)]
  have hY : 2 * C * B * Real.sqrt E ≤ E + C ^ 2 * B ^ 2 := by
    nlinarith [sq_nonneg (Real.sqrt E - C * B)]
  have hAB' := mul_le_mul_of_nonneg_left hAB hC0
  nlinarith [hE]

end Hormander.D

end

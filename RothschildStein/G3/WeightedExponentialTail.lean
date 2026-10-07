-- Copyright (c) 2026 Scott Armstrong and Amélie Loher. All rights reserved.
-- Released under Apache 2.0 license as described in the file LICENSE.
module
public import RothschildStein.G3.BCH
@[expose] public section
noncomputable section
namespace RothschildStein.G3

/-- The exponential tail of a weight-k input starts at weight 2k
(BB Lemma 9.26, pp. 417–419; filtered coefficient calculation). -/
theorem expTail_weight_order {a s k : ℕ} {p : Fin a → ℕ+}
    {f : FiniteWordAlgebra a s p} (hf : FiniteOrderAtLeast k f) :
    FiniteOrderAtLeast (2 * k) (expTail f) := by
  apply finiteOrderAtLeast_sum
  intro n _
  apply finiteOrderAtLeast_smul
  apply finiteOrderAtLeast_mono (finiteOrderAtLeast_pow hf (n + 2))
  exact Nat.mul_le_mul_right k (by omega : 2 ≤ n + 2)

/-- Exponentiation preserves the input's weighted order after removal
of its constant unit (BB Lemma 9.26, pp. 417–419). -/
theorem finiteExp_sub_one_weight_order {a s k : ℕ} {p : Fin a → ℕ+}
    {f : FiniteWordAlgebra a s p} (hf : FiniteOrderAtLeast k f) :
    FiniteOrderAtLeast k (finiteExp f - 1) := by
  have he : finiteExp f - 1 = f + expTail f := by rw [finiteExp_eq]; abel
  rw [he]
  exact finiteOrderAtLeast_add hf (finiteOrderAtLeast_mono (expTail_weight_order hf) (by omega))

/-- The exact finite logarithm retains every weighted lower-order bound
(BB Lemma 9.26, pp. 417–419; explicit correction induction). -/
theorem logApprox_weight_order {a s k : ℕ} {p : Fin a → ℕ+}
    {v : FiniteWordAlgebra a s p} (hv : FiniteOrderAtLeast k v) (n : ℕ) :
    FiniteOrderAtLeast k (logApprox v n) := by
  induction n with
  | zero => exact finiteOrderAtLeast_zero_element k
  | succ n ih =>
    have he : 1 + v - finiteExp (logApprox v n) =
        v - (finiteExp (logApprox v n) - 1) := by abel
    rw [logApprox, he]
    exact finiteOrderAtLeast_add ih (finiteOrderAtLeast_sub hv (finiteExp_sub_one_weight_order ih))

/-- Logarithm differs from its linear input only at twice the input
weight (BB Lemma 9.26, pp. 417–419; explicit correction induction). -/
theorem logApprox_sub_input_weight_order {a s k : ℕ} {p : Fin a → ℕ+}
    {v : FiniteWordAlgebra a s p} (hv : FiniteOrderAtLeast k v) {n : ℕ} (hn : 1 ≤ n) :
    FiniteOrderAtLeast (2 * k) (logApprox v n - v) := by
  obtain ⟨m, rfl⟩ := Nat.exists_eq_succ_of_ne_zero (by omega : n ≠ 0)
  have he : logApprox v (m + 1) - v = -expTail (logApprox v m) := by
    rw [logApprox, finiteExp_eq]
    abel
  rw [he]
  simpa only [neg_one_smul] using
    finiteOrderAtLeast_smul (expTail_weight_order (logApprox_weight_order hv m)) (-1 : ℝ)
end RothschildStein.G3

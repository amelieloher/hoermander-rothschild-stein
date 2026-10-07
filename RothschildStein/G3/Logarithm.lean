-- Copyright (c) 2026 Scott Armstrong and Amélie Loher. All rights reserved.
-- Released under Apache 2.0 license as described in the file LICENSE.
module
public import RothschildStein.G3.Exponential
@[expose] public section
noncomputable section
namespace RothschildStein.G3

/-- Successive coefficient correction for the logarithm of 1+v.
Each correction fixes one further weighted layer (BB Lemma 9.69, pp. 470–471). -/
def logApprox {a s : ℕ} {p : Fin a → ℕ+} (v : FiniteWordAlgebra a s p) :
    ℕ → FiniteWordAlgebra a s p
  | 0 => 0
  | n + 1 => logApprox v n + (1 + v - finiteExp (logApprox v n))

/-- Exponentiation sends zero to the unit (BB p. 468). -/
@[simp] theorem finiteExp_zero {a s : ℕ} {p : Fin a → ℕ+} :
    finiteExp (0 : FiniteWordAlgebra a s p) = 1 := by
  rw [finiteExp_eq]
  simp [expTail, pow_succ]

/-- Correcting the exponential error raises its weighted order
(BB Lemma 9.69, pp. 470–471). -/
theorem logApprox_step {a s : ℕ} {p : Fin a → ℕ+} {k : ℕ}
    {v f : FiniteWordAlgebra a s p} (hf : FiniteOrderAtLeast 1 f)
    (he : FiniteOrderAtLeast k (1 + v - finiteExp f))
    (hk : 1 ≤ k) :
    FiniteOrderAtLeast 1 (f + (1 + v - finiteExp f)) ∧
    FiniteOrderAtLeast (k + 1)
      (1 + v - finiteExp (f + (1 + v - finiteExp f))) := by
  let e := 1 + v - finiteExp f
  have he' : FiniteOrderAtLeast k e := he
  have hnew := finiteOrderAtLeast_add hf (finiteOrderAtLeast_mono he' hk)
  have hd : FiniteOrderAtLeast k ((f + e) - f) := by
    simpa only [add_sub_cancel_left] using he'
  have h := finiteExp_sub_linear_order hnew hf hd
  have hid : 1 + v - finiteExp (f + e) =
      -(finiteExp (f + e) - finiteExp f - ((f + e) - f)) := by
    dsimp [e]
    abel
  refine ⟨hnew, ?_⟩
  rw [hid]
  have hn := finiteOrderAtLeast_sub (finiteOrderAtLeast_zero_element (k + 1)) h
  simpa only [zero_sub] using hn

/-- The nth coefficient correction leaves error of order n+1
(BB Lemma 9.69, pp. 470–471). -/
theorem logApprox_order {a s : ℕ} {p : Fin a → ℕ+}
    {v : FiniteWordAlgebra a s p} (hv : FiniteOrderAtLeast 1 v) (n : ℕ) :
    FiniteOrderAtLeast 1 (logApprox v n) ∧
      FiniteOrderAtLeast (n + 1) (1 + v - finiteExp (logApprox v n)) := by
  induction n with
  | zero =>
    constructor
    · exact finiteOrderAtLeast_zero_element 1
    · simpa only [logApprox, finiteExp_zero, add_sub_cancel_left, Nat.zero_add] using hv
  | succ n ih => exact logApprox_step ih.1 ih.2 (by omega)

/-- The coefficient recursion gives an exact logarithm in the finite quotient
(BB Lemma 9.69, pp. 470–471). -/
theorem finiteExp_logApprox {a s : ℕ} {p : Fin a → ℕ+}
    {v : FiniteWordAlgebra a s p} (hv : FiniteOrderAtLeast 1 v) :
    finiteExp (logApprox v s) = 1 + v := by
  have hz := eq_zero_of_finiteOrderAtLeast_gt (logApprox_order hv s).2 (by omega)
  exact (sub_eq_zero.mp hz).symm

end RothschildStein.G3

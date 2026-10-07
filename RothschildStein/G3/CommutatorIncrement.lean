-- Copyright (c) 2026 Scott Armstrong and Amélie Loher. All rights reserved.
-- Released under Apache 2.0 license as described in the file LICENSE.
module
public import RothschildStein.G3.ExponentialCommutatorTail
@[expose] public section
noncomputable section
namespace RothschildStein.G3

/-- The signed four-exponential product in pullback order
(BB Lemma 9.26, pp. 417–419; corrected sign). -/
def commutatorIncrement {a s : ℕ} {p : Fin a → ℕ+}
    (A B : FiniteWordAlgebra a s p) : FiniteWordAlgebra a s p :=
  finiteExp A * finiteExp B * finiteExp (-A) * finiteExp (-B) - 1

/-- Positive-order exponentials have their exact negative inverse
(BB (9.14), p. 417). -/
theorem finiteExp_mul_neg_eq_one {a s : ℕ} {p : Fin a → ℕ+}
    {A : FiniteWordAlgebra a s p} (hA : FiniteOrderAtLeast 1 A) :
    finiteExp A * finiteExp (-A) = 1 := by
  have hn : FiniteOrderAtLeast 1 (-A) := by
    simpa only [zero_sub] using finiteOrderAtLeast_sub (finiteOrderAtLeast_zero_element 1) hA
  rw [← finiteExp_BCH hA hn, finiteBCH_neg_right hA, finiteExp_zero]

/-- Cancellation isolates the exponential commutator
(BB Lemma 9.26, pp. 417–419). -/
theorem commutatorIncrement_eq {a s : ℕ} {p : Fin a → ℕ+}
    {A B : FiniteWordAlgebra a s p} (hA : FiniteOrderAtLeast 1 A)
    (hB : FiniteOrderAtLeast 1 B) :
    commutatorIncrement A B = ⁅finiteExp A, finiteExp B⁆ *
      (finiteExp (-A) * finiteExp (-B)) := by
  have hc : finiteExp B * finiteExp A * (finiteExp (-A) * finiteExp (-B)) = 1 := by
    rw [mul_assoc, ← mul_assoc (finiteExp A), finiteExp_mul_neg_eq_one hA, one_mul,
      finiteExp_mul_neg_eq_one hB]
  rw [Ring.lie_def, sub_mul, hc, commutatorIncrement]
  simp only [mul_assoc]

/-- The signed group commutator has no term below the sum of input
weights (BB Lemma 9.26, pp. 417–419). -/
theorem commutatorIncrement_weight_order {a s k l : ℕ} {p : Fin a → ℕ+}
    {A B : FiniteWordAlgebra a s p} (hk : 1 ≤ k) (hl : 1 ≤ l)
    (hA : FiniteOrderAtLeast k A) (hB : FiniteOrderAtLeast l B) :
    FiniteOrderAtLeast (k + l) (commutatorIncrement A B) := by
  rw [commutatorIncrement_eq (finiteOrderAtLeast_mono hA hk) (finiteOrderAtLeast_mono hB hl)]
  simpa only [Nat.add_zero] using finiteOrderAtLeast_mul
    (exponential_bracket_weight_order hA hB)
    (finiteOrderAtLeast_zero (finiteExp (-A) * finiteExp (-B)))
end RothschildStein.G3

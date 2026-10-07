-- Copyright (c) 2026 Scott Armstrong and Amélie Loher. All rights reserved.
-- Released under Apache 2.0 license as described in the file LICENSE.
module

public import Hormander.B.Fractional.DerivativeFacts

@[expose] public section

noncomputable section

namespace Hormander.B

variable {N : ℕ}

/-- (hypothesis class) Differential operators with Schwartz coefficients of order at most `m`: finite sums of
`M_a ∘ ∂_{i₁} ∘ ⋯ ∘ ∂_{i_k}` with `k ≤ m`, built by right composition with coordinate
derivatives. -/
inductive IsDiffOp : ℕ → Operator N → Prop
  | mult (m : ℕ) (g : TestFunction N) : IsDiffOp m (multiplierOperator g)
  | add {m : ℕ} {P Q : Operator N} : IsDiffOp m P → IsDiffOp m Q → IsDiffOp m (P + Q)
  | derivRight {m : ℕ} {P : Operator N} (i : Fin N) :
      IsDiffOp m P → IsDiffOp (m + 1) (P.comp (coordinateDerivative i))

theorem IsDiffOp.hasOrder {m : ℕ} {P : Operator N} (h : IsDiffOp m P) : HasOrder m P := by
  induction h with
  | mult m g => exact (hasOrder_multiplierOperator_zero g).mono (by positivity)
  | add _ _ ihP ihQ => exact ihP.add ihQ
  | derivRight i _ ih =>
    have := ih.comp (hasOrder_coordinateDerivative i)
    push_cast
    exact this

/-- The commutator of a coordinate derivative with a differential operator has the same order. -/
theorem IsDiffOp.comm_coordinateDerivative {m : ℕ} {P : Operator N} (h : IsDiffOp m P)
    (j : Fin N) : IsDiffOp m (operatorComm (coordinateDerivative j) P) := by
  induction h with
  | mult m g =>
    rw [operatorComm_coordinateDerivative_multiplier]
    exact IsDiffOp.mult m _
  | add _ _ ihP ihQ =>
    rw [operatorComm_add_right]
    exact ihP.add ihQ
  | derivRight i _ ih =>
    rw [operatorComm_comp_right, operatorComm_coordinateDerivative_coordinateDerivative,
      LinearMap.comp_zero, add_zero]
    exact ih.derivRight i

theorem operatorComm_lambda_comp_coordinateDerivative (σ : ℝ) (X : Operator N) (i : Fin N) :
    operatorComm (lambdaOperator σ) (X.comp (coordinateDerivative i)) =
      (operatorComm (lambdaOperator σ) X).comp (coordinateDerivative i) := by
  rw [operatorComm_comp_right, operatorComm_lambda_coordinateDerivative, LinearMap.comp_zero,
    add_zero]

/-- (first claim) `[Λ^σ, P]` has order `m + σ - 1`. -/
theorem fractional_diffOp_order (σ : ℝ) {m : ℕ} {P : Operator N} (h : IsDiffOp m P) :
    HasOrder ((m : ℝ) + σ - 1) (operatorComm (lambdaOperator σ) P) := by
  induction h with
  | mult m g =>
    refine (fractionalCommutator_order σ g).mono ?_
    have : (0 : ℝ) ≤ m := Nat.cast_nonneg m
    linarith
  | add _ _ ihP ihQ =>
    rw [operatorComm_add_right]
    exact ihP.add ihQ
  | derivRight i _ ih =>
    rw [operatorComm_lambda_comp_coordinateDerivative]
    have := ih.comp (hasOrder_coordinateDerivative i)
    push_cast
    convert this using 1
    ring

/-- The nested commutator against a multiplier, by induction on the first operator. -/
theorem fractional_diffOp_nested_mult (σ : ℝ) {m : ℕ} {P : Operator N} (hP : IsDiffOp m P)
    (n : ℕ) (b : TestFunction N) :
    HasOrder ((m : ℝ) + n + σ - 2)
      (operatorComm (operatorComm (lambdaOperator σ) P) (multiplierOperator b)) := by
  have hn : (0 : ℝ) ≤ n := Nat.cast_nonneg n
  induction hP with
  | mult m g =>
    refine (fractionalCommutator_nested_order σ g b).mono ?_
    have : (0 : ℝ) ≤ m := Nat.cast_nonneg m
    linarith
  | add _ _ ihP ihQ =>
    rw [operatorComm_add_right, operatorComm_add_left]
    exact ihP.add ihQ
  | @derivRight m' P' i hP' ih =>
    rw [operatorComm_lambda_comp_coordinateDerivative, operatorComm_comp_left,
      operatorComm_coordinateDerivative_multiplier]
    have hA := fractional_diffOp_order σ hP'
    have t1 : HasOrder ((m' : ℝ) + σ - 1)
        ((operatorComm (lambdaOperator σ) P').comp
          (multiplierOperator (coordinateDerivative i b))) := by
      simpa using hA.comp (hasOrder_multiplierOperator_zero (coordinateDerivative i b))
    have t2 := ih.comp (hasOrder_coordinateDerivative i)
    push_cast
    refine (t1.mono ?_).add (t2.mono ?_)
    · linarith
    · linarith

/-- (third claim) `[[Λ^σ, P], Q]` has order `m + n + σ - 2`. -/
theorem fractional_diffOp_nested_order (σ : ℝ) {m n : ℕ} {P Q : Operator N}
    (hP : IsDiffOp m P) (hQ : IsDiffOp n Q) :
    HasOrder ((m : ℝ) + n + σ - 2) (operatorComm (operatorComm (lambdaOperator σ) P) Q) := by
  induction hQ generalizing m P with
  | mult n b => exact fractional_diffOp_nested_mult σ hP n b
  | add _ _ ihP ihQ =>
    rw [operatorComm_add_right]
    exact (ihP hP).add (ihQ hP)
  | @derivRight n' Q' j hQ' ih =>
    rw [operatorComm_comp_right]
    have e : operatorComm (operatorComm (lambdaOperator σ) P) (coordinateDerivative j) =
        (-1 : ℂ) • operatorComm (lambdaOperator σ) (operatorComm (coordinateDerivative j) P) := by
      have h0 : operatorComm (coordinateDerivative j) (lambdaOperator σ) = (0 : Operator N) := by
        rw [operatorComm_antisymm, operatorComm_lambda_coordinateDerivative, smul_zero]
      have h00 : operatorComm (0 : Operator N) P = 0 := by
        ext u; simp [operatorComm]
      rw [operatorComm_antisymm (operatorComm (lambdaOperator σ) P), operatorComm_jacobi, h0, h00,
        zero_add]
    rw [e]
    have t1 := (ih hP).comp (hasOrder_coordinateDerivative j)
    have t2 := hQ'.hasOrder.comp
      (((fractional_diffOp_order σ (hP.comm_coordinateDerivative j))).smul (-1 : ℂ))
    push_cast
    refine (t1.mono ?_).add (t2.mono ?_)
    · linarith
    · linarith

theorem IsDiffOp.mono {m : ℕ} {P : Operator N} (h : IsDiffOp m P) {m' : ℕ} (hm : m ≤ m') :
    IsDiffOp m' P := by
  induction h generalizing m' with
  | mult m g => exact IsDiffOp.mult m' g
  | add _ _ ihP ihQ => exact (ihP hm).add (ihQ hm)
  | @derivRight m P i _ ih =>
    cases m' with
    | zero => omega
    | succ k => exact (ih (by omega)).derivRight i

/-- The iterated coordinate derivative attached to a word of indices. -/
def derivWord : List (Fin N) → Operator N
  | [] => LinearMap.id
  | i :: w => (derivWord w).comp (coordinateDerivative i)

theorem multiplierOperator_zero : multiplierOperator (0 : TestFunction N) = 0 := by
  ext u x
  simp [multiplierOperator_apply]

end Hormander.B

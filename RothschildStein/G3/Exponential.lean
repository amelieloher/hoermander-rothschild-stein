-- Copyright (c) 2026 Scott Armstrong and Amélie Loher. All rights reserved.
-- Released under Apache 2.0 license as described in the file LICENSE.
module
public import RothschildStein.G3.FilteredOperations
public import Mathlib.Tactic.NoncommRing
@[expose] public section
noncomputable section
open scoped BigOperators
namespace RothschildStein.G3

/-- The exponential is a finite polynomial in the weighted quotient.
The extra top power is zero for positive-order arguments (BB pp. 467–469). -/
def finiteExp {a s : ℕ} {p : Fin a → ℕ+} (f : FiniteWordAlgebra a s p) :
    FiniteWordAlgebra a s p :=
  ∑ n ∈ Finset.range (s + 2), ((n.factorial : ℝ)⁻¹) • f ^ n

/-- Nonlinear part of the finite exponential (BB pp. 467–469). -/
def expTail {a s : ℕ} {p : Fin a → ℕ+} (f : FiniteWordAlgebra a s p) :
    FiniteWordAlgebra a s p :=
  ∑ n ∈ Finset.range s, (((n + 2).factorial : ℝ)⁻¹) • f ^ (n + 2)

/-- The exponential has constant and linear terms 1 and f (BB p. 469). -/
theorem finiteExp_eq {a s : ℕ} {p : Fin a → ℕ+} (f : FiniteWordAlgebra a s p) :
    finiteExp f = 1 + f + expTail f := by
  unfold finiteExp expTail
  rw [Finset.sum_range_succ', Finset.sum_range_succ']
  simp only [Nat.factorial_zero, Nat.factorial_one, Nat.cast_one, inv_one,
    pow_zero, pow_one, one_smul, Nat.zero_add]
  abel

/-- Difference of powers gains n−1 orders beyond the argument difference
(BB pp. 475–476, coefficientwise injectivity argument). -/
theorem finiteOrderAtLeast_pow_sub {a s : ℕ} {p : Fin a → ℕ+} {k : ℕ}
    {f g : FiniteWordAlgebra a s p} (hf : FiniteOrderAtLeast 1 f)
    (hg : FiniteOrderAtLeast 1 g) (hd : FiniteOrderAtLeast k (f - g)) (n : ℕ) :
    FiniteOrderAtLeast (k + n) (f ^ (n + 1) - g ^ (n + 1)) := by
  induction n with
  | zero => simpa only [Nat.add_zero, Nat.zero_add, pow_one] using hd
  | succ n ih =>
    have he : f ^ (n + 1 + 1) - g ^ (n + 1 + 1) =
        (f ^ (n + 1) - g ^ (n + 1)) * f + g ^ (n + 1) * (f - g) := by
      simp only [pow_succ]
      noncomm_ring
    rw [he]
    have h₁ := finiteOrderAtLeast_mul ih hf
    have h₂ := finiteOrderAtLeast_mul (finiteOrderAtLeast_pow hg (n + 1)) hd
    apply finiteOrderAtLeast_add
    · simpa only [Nat.add_assoc] using h₁
    · simpa only [Nat.mul_one, Nat.add_comm, Nat.add_left_comm, Nat.add_assoc] using h₂

/-- The exponential tail difference gains one full weighted order
(BB pp. 475–476). -/
theorem expTail_sub_order {a s : ℕ} {p : Fin a → ℕ+} {k : ℕ}
    {f g : FiniteWordAlgebra a s p} (hf : FiniteOrderAtLeast 1 f)
    (hg : FiniteOrderAtLeast 1 g) (hd : FiniteOrderAtLeast k (f - g)) :
    FiniteOrderAtLeast (k + 1) (expTail f - expTail g) := by
  unfold expTail
  rw [← Finset.sum_sub_distrib]
  apply finiteOrderAtLeast_sum
  intro n _
  rw [← smul_sub]
  apply finiteOrderAtLeast_smul
  apply finiteOrderAtLeast_mono (finiteOrderAtLeast_pow_sub hf hg hd (n + 1))
  omega

/-- Exponential differences are triangular with respect to weighted order
(BB pp. 475–476). -/
theorem finiteExp_sub_linear_order {a s : ℕ} {p : Fin a → ℕ+} {k : ℕ}
    {f g : FiniteWordAlgebra a s p} (hf : FiniteOrderAtLeast 1 f)
    (hg : FiniteOrderAtLeast 1 g) (hd : FiniteOrderAtLeast k (f - g)) :
    FiniteOrderAtLeast (k + 1) (finiteExp f - finiteExp g - (f - g)) := by
  have he : finiteExp f - finiteExp g - (f - g) = expTail f - expTail g := by
    rw [finiteExp_eq, finiteExp_eq]
    abel
  rw [he]
  exact expTail_sub_order hf hg hd

/-- Exponentiation is injective on positive-weight elements of every finite
weighted quotient (BB Proposition 9.72, pp. 475–476). -/
theorem finiteExp_injective_positive {a s : ℕ} {p : Fin a → ℕ+}
    {f g : FiniteWordAlgebra a s p} (hf : FiniteOrderAtLeast 1 f)
    (hg : FiniteOrderAtLeast 1 g) (he : finiteExp f = finiteExp g) : f = g := by
  have hd : ∀ k, FiniteOrderAtLeast k (f - g) := by
    intro k
    induction k with
    | zero => exact finiteOrderAtLeast_zero _
    | succ k ih =>
      have h := finiteExp_sub_linear_order hf hg ih
      rw [he, sub_self, zero_sub] at h
      have hn := finiteOrderAtLeast_sub (finiteOrderAtLeast_zero_element (k + 1)) h
      simpa only [zero_sub, neg_neg] using hn
  exact sub_eq_zero.mp (eq_zero_of_finiteOrderAtLeast_gt (hd (s + 1)) (by omega))

end RothschildStein.G3

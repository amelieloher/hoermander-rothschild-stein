-- Copyright (c) 2026 Scott Armstrong and Amélie Loher. All rights reserved.
-- Released under Apache 2.0 license as described in the file LICENSE.
module
public import RothschildStein.G3.FiniteAlgebra
public import RothschildStein.G3.Homogeneity
public import Mathlib.RingTheory.Nilpotent.Defs
@[expose] public section
noncomputable section
namespace RothschildStein.G3

/-- Weighted order filtration on associative coefficients (BB pp. 524–525). -/
def OrderAtLeast {a : ℕ} (p : Fin a → ℕ+) (k : ℕ)
    (f : List (Fin a) → ℝ) : Prop :=
  ∀ J, wordWeight p J < k → f J = 0

/-- Cauchy multiplication adds weighted lower orders (BB p. 525). -/
theorem orderAtLeast_convolution {a : ℕ} (p : Fin a → ℕ+) {k l : ℕ}
    {f g : List (Fin a) → ℝ} (hf : OrderAtLeast p k f) (hg : OrderAtLeast p l g) :
    OrderAtLeast p (k + l) (wordConvolution f g) := by
  intro J hJ
  unfold wordConvolution
  apply Finset.sum_eq_zero
  intro r _
  have hw := weight_append p (J.take r) (J.drop r)
  rw [List.take_append_drop] at hw
  by_cases hpre : wordWeight p (J.take r) < k
  · rw [hf _ hpre, zero_mul]
  · rw [hg _ (by omega), mul_zero]

/-- Weighted lower order in the finite quotient (BB p. 525). -/
def FiniteOrderAtLeast {a s : ℕ} {p : Fin a → ℕ+} (k : ℕ)
    (f : FiniteWordAlgebra a s p) : Prop := OrderAtLeast p k (extend f)

/-- Restriction followed by extension preserves weighted lower order
(BB Proposition 10.44, p. 525). -/
theorem orderAtLeast_extend_restrict {a s : ℕ} {p : Fin a → ℕ+} {k : ℕ}
    {f : List (Fin a) → ℝ} (hf : OrderAtLeast p k f) :
    OrderAtLeast p k (extend (restrict f : WordCoefficients a s p)) := by
  intro J hJ
  by_cases h : wordWeight p J ≤ s
  · rw [extend_restrict f J h]
    exact hf J hJ
  · simp [extend, h]

/-- Multiplication adds lower orders in the truncated quotient (BB p. 525). -/
theorem finiteOrderAtLeast_mul {a s : ℕ} {p : Fin a → ℕ+} {k l : ℕ}
    {f g : FiniteWordAlgebra a s p}
    (hf : FiniteOrderAtLeast k f) (hg : FiniteOrderAtLeast l g) :
    FiniteOrderAtLeast (k + l) (f * g) :=
  orderAtLeast_extend_restrict (orderAtLeast_convolution p hf hg)

/-- Every quotient coefficient has nonnegative weighted order (BB p. 525). -/
theorem finiteOrderAtLeast_zero {a s : ℕ} {p : Fin a → ℕ+}
    (f : FiniteWordAlgebra a s p) : FiniteOrderAtLeast 0 f := by
  intro J hJ
  omega

/-- Powers accumulate weighted order (BB Proposition 10.44, p. 525). -/
theorem finiteOrderAtLeast_pow {a s : ℕ} {p : Fin a → ℕ+} {k : ℕ}
    {f : FiniteWordAlgebra a s p} (hf : FiniteOrderAtLeast k f) (n : ℕ) :
    FiniteOrderAtLeast (n * k) (f ^ n) := by
  induction n with
  | zero =>
    simp only [Nat.zero_mul]
    exact finiteOrderAtLeast_zero _
  | succ n ih =>
    rw [pow_succ, Nat.succ_mul]
    exact finiteOrderAtLeast_mul ih hf

/-- An element whose lower order exceeds the cutoff is zero (BB p. 525). -/
theorem eq_zero_of_finiteOrderAtLeast_gt {a s : ℕ} {p : Fin a → ℕ+}
    {k : ℕ} {f : FiniteWordAlgebra a s p} (hf : FiniteOrderAtLeast k f) (hk : s < k) :
    f = 0 := by
  funext J
  have h := hf J.val (lt_of_le_of_lt (boundedWord_weight J) hk)
  change f J = 0
  simp only [extend] at h
  split at h
  · exact h
  · rename_i hb
    exact False.elim (hb (boundedWord_weight J))

/-- Every positive-order element is nilpotent, with exponent at most s+1
(BB Proposition 10.44, p. 525). -/
theorem pow_cutoff_eq_zero {a s : ℕ} {p : Fin a → ℕ+}
    {f : FiniteWordAlgebra a s p} (hf : FiniteOrderAtLeast 1 f) : f ^ (s + 1) = 0 := by
  apply eq_zero_of_finiteOrderAtLeast_gt (finiteOrderAtLeast_pow hf (s + 1))
  simp

/-- Nilpotence of the positive-weight associative ideal (BB p. 525). -/
theorem isNilpotent_of_positive_order {a s : ℕ} {p : Fin a → ℕ+}
    {f : FiniteWordAlgebra a s p} (hf : FiniteOrderAtLeast 1 f) : IsNilpotent f :=
  ⟨s + 1, pow_cutoff_eq_zero hf⟩

end RothschildStein.G3

-- Copyright (c) 2026 Scott Armstrong and Amélie Loher. All rights reserved.
-- Released under Apache 2.0 license as described in the file LICENSE.
module
public import RothschildStein.G3.Logarithm
public import Mathlib.RingTheory.Nilpotent.Exp
@[expose] public section
noncomputable section
open scoped BigOperators
namespace RothschildStein.G3

instance finiteWordRationalAlgebra {a s : ℕ} {p : Fin a → ℕ+} : Algebra ℚ (FiniteWordAlgebra a s p) :=
  Algebra.compHom (FiniteWordAlgebra a s p) (algebraMap ℚ ℝ)

/-- The nonlinear exponential tail starts at weight two (BB pp. 467–469). -/
theorem expTail_order {a s : ℕ} {p : Fin a → ℕ+}
    {f : FiniteWordAlgebra a s p} (hf : FiniteOrderAtLeast 1 f) :
    FiniteOrderAtLeast 2 (expTail f) := by
  apply finiteOrderAtLeast_sum
  intro n _
  apply finiteOrderAtLeast_smul
  apply finiteOrderAtLeast_mono (finiteOrderAtLeast_pow hf (n + 2))
  omega

/-- Exponentials of positive-order elements have unit constant term (BB p. 468). -/
theorem finiteExp_sub_one_order {a s : ℕ} {p : Fin a → ℕ+}
    {f : FiniteWordAlgebra a s p} (hf : FiniteOrderAtLeast 1 f) :
    FiniteOrderAtLeast 1 (finiteExp f - 1) := by
  have he : finiteExp f - 1 = f + expTail f := by rw [finiteExp_eq]; abel
  rw [he]
  exact finiteOrderAtLeast_add hf (finiteOrderAtLeast_mono (expTail_order hf) (by omega))

/-- Products of exponentials retain unit constant term (BB p. 470). -/
theorem finiteExp_product_sub_one_order {a s : ℕ} {p : Fin a → ℕ+}
    {f g : FiniteWordAlgebra a s p} (hf : FiniteOrderAtLeast 1 f)
    (hg : FiniteOrderAtLeast 1 g) : FiniteOrderAtLeast 1 (finiteExp f * finiteExp g - 1) := by
  have h₁ := finiteExp_sub_one_order hf
  have h₂ := finiteExp_sub_one_order hg
  have he : finiteExp f * finiteExp g - 1 =
      (finiteExp f - 1) + (finiteExp g - 1) + (finiteExp f - 1) * (finiteExp g - 1) := by
    noncomm_ring
  rw [he]
  exact finiteOrderAtLeast_add (finiteOrderAtLeast_add h₁ h₂)
    (finiteOrderAtLeast_mono (finiteOrderAtLeast_mul h₁ h₂) (by omega))

/-- BCH in the finite associative weighted quotient, defined by the unique
positive-order logarithm of exp(f)exp(g) (BB Theorem 9.68, pp. 469–471).
Membership in the Lie span is a separate assertion. -/
def finiteBCH {a s : ℕ} {p : Fin a → ℕ+} (f g : FiniteWordAlgebra a s p) :
    FiniteWordAlgebra a s p := logApprox (finiteExp f * finiteExp g - 1) s

/-- The finite BCH logarithm has positive order (BB pp. 470–471). -/
theorem finiteBCH_order {a s : ℕ} {p : Fin a → ℕ+}
    {f g : FiniteWordAlgebra a s p} (hf : FiniteOrderAtLeast 1 f)
    (hg : FiniteOrderAtLeast 1 g) : FiniteOrderAtLeast 1 (finiteBCH f g) :=
  (logApprox_order (finiteExp_product_sub_one_order hf hg) s).1

/-- The defining exponential identity for finite BCH (BB (9.76), p. 470). -/
theorem finiteExp_BCH {a s : ℕ} {p : Fin a → ℕ+}
    {f g : FiniteWordAlgebra a s p} (hf : FiniteOrderAtLeast 1 f)
    (hg : FiniteOrderAtLeast 1 g) : finiteExp (finiteBCH f g) = finiteExp f * finiteExp g := by
  unfold finiteBCH
  rw [finiteExp_logApprox (finiteExp_product_sub_one_order hf hg)]
  abel

/-- Associativity survives every finite positive weighted truncation
(BB Proposition 9.72, pp. 474–476). -/
theorem finiteBCH_assoc {a s : ℕ} {p : Fin a → ℕ+}
    {f g h : FiniteWordAlgebra a s p} (hf : FiniteOrderAtLeast 1 f)
    (hg : FiniteOrderAtLeast 1 g) (hh : FiniteOrderAtLeast 1 h) :
    finiteBCH (finiteBCH f g) h = finiteBCH f (finiteBCH g h) := by
  apply finiteExp_injective_positive
    (finiteBCH_order (finiteBCH_order hf hg) hh)
    (finiteBCH_order hf (finiteBCH_order hg hh))
  rw [finiteExp_BCH (finiteBCH_order hf hg) hh,
    finiteExp_BCH hf (finiteBCH_order hg hh), finiteExp_BCH hf hg,
    finiteExp_BCH hg hh, mul_assoc]

/-- Zero is the right identity for finite BCH (BB p. 474). -/
theorem finiteBCH_zero_right {a s : ℕ} {p : Fin a → ℕ+}
    {f : FiniteWordAlgebra a s p} (hf : FiniteOrderAtLeast 1 f) : finiteBCH f 0 = f := by
  apply finiteExp_injective_positive (finiteBCH_order hf (finiteOrderAtLeast_zero_element 1)) hf
  rw [finiteExp_BCH hf (finiteOrderAtLeast_zero_element 1), finiteExp_zero, mul_one]

/-- Zero is the left identity for finite BCH (BB p. 474). -/
theorem finiteBCH_zero_left {a s : ℕ} {p : Fin a → ℕ+}
    {f : FiniteWordAlgebra a s p} (hf : FiniteOrderAtLeast 1 f) : finiteBCH 0 f = f := by
  apply finiteExp_injective_positive (finiteBCH_order (finiteOrderAtLeast_zero_element 1) hf) hf
  rw [finiteExp_BCH (finiteOrderAtLeast_zero_element 1) hf, finiteExp_zero, one_mul]

/-- Agreement with Mathlib's nilpotent exponential on positive-order elements
(BB p. 468). -/
theorem finiteExp_eq_nilpotentExp {a s : ℕ} {p : Fin a → ℕ+}
    {f : FiniteWordAlgebra a s p} (hf : FiniteOrderAtLeast 1 f) :
    finiteExp f = IsNilpotent.exp f := by
  rw [IsNilpotent.exp_eq_sum (k := s + 2) (pow_eq_zero_of_le (by omega) (pow_cutoff_eq_zero hf))]
  unfold finiteExp
  apply Finset.sum_congr rfl
  intro n _
  have he := ratCast_smul_eq ℚ ℝ ((n.factorial : ℚ)⁻¹) (f ^ n)
  simpa only [Rat.cast_id, Rat.cast_inv, Rat.cast_natCast] using he.symm

/-- Negation is a right inverse for finite BCH (BB p. 474). -/
theorem finiteBCH_neg_right {a s : ℕ} {p : Fin a → ℕ+}
    {f : FiniteWordAlgebra a s p} (hf : FiniteOrderAtLeast 1 f) : finiteBCH f (-f) = 0 := by
  have hn : FiniteOrderAtLeast 1 (-f) := by
    simpa only [zero_sub] using finiteOrderAtLeast_sub (finiteOrderAtLeast_zero_element 1) hf
  apply finiteExp_injective_positive (finiteBCH_order hf hn) (finiteOrderAtLeast_zero_element 1)
  rw [finiteExp_BCH hf hn, finiteExp_zero, finiteExp_eq_nilpotentExp hf,
    finiteExp_eq_nilpotentExp hn]
  exact IsNilpotent.exp_mul_exp_neg_self (isNilpotent_of_positive_order hf)

/-- Negation is a left inverse for finite BCH (BB p. 474). -/
theorem finiteBCH_neg_left {a s : ℕ} {p : Fin a → ℕ+}
    {f : FiniteWordAlgebra a s p} (hf : FiniteOrderAtLeast 1 f) : finiteBCH (-f) f = 0 := by
  have hn : FiniteOrderAtLeast 1 (-f) := by
    simpa only [zero_sub] using finiteOrderAtLeast_sub (finiteOrderAtLeast_zero_element 1) hf
  apply finiteExp_injective_positive (finiteBCH_order hn hf) (finiteOrderAtLeast_zero_element 1)
  rw [finiteExp_BCH hn hf, finiteExp_zero, finiteExp_eq_nilpotentExp hn,
    finiteExp_eq_nilpotentExp hf]
  exact IsNilpotent.exp_neg_mul_exp_self (isNilpotent_of_positive_order hf)

/-- BCH of commuting arguments is their sum (BB Lemma 9.71, p. 471). -/
theorem finiteBCH_eq_add_of_commute {a s : ℕ} {p : Fin a → ℕ+}
    {f g : FiniteWordAlgebra a s p} (hf : FiniteOrderAtLeast 1 f)
    (hg : FiniteOrderAtLeast 1 g) (hfg : Commute f g) : finiteBCH f g = f + g := by
  have hs := finiteOrderAtLeast_add hf hg
  apply finiteExp_injective_positive (finiteBCH_order hf hg) hs
  rw [finiteExp_BCH hf hg, finiteExp_eq_nilpotentExp hf,
    finiteExp_eq_nilpotentExp hg, finiteExp_eq_nilpotentExp hs]
  exact (IsNilpotent.exp_add_of_commute hfg (isNilpotent_of_positive_order hf)
    (isNilpotent_of_positive_order hg)).symm

/-- Finite positive-degree algebra substitutions preserve exponentiation
(BB (9.75), p. 468). -/
theorem map_finiteExp {a s b t : ℕ} {p : Fin a → ℕ+} {q : Fin b → ℕ+}
    (F : FiniteWordAlgebra a s p →ₐ[ℝ] FiniteWordAlgebra b t q)
    {f : FiniteWordAlgebra a s p} (hf : FiniteOrderAtLeast 1 f)
    (hFf : FiniteOrderAtLeast 1 (F f)) : F (finiteExp f) = finiteExp (F f) := by
  rw [finiteExp_eq_nilpotentExp hf, finiteExp_eq_nilpotentExp hFf]
  exact IsNilpotent.map_exp (isNilpotent_of_positive_order hf) F

/-- Positive-degree algebra substitutions preserve finite BCH
(BB (9.75), p. 468; Proposition 9.72, pp. 474–476). -/
theorem map_finiteBCH {a s b t : ℕ} {p : Fin a → ℕ+} {q : Fin b → ℕ+}
    (F : FiniteWordAlgebra a s p →ₐ[ℝ] FiniteWordAlgebra b t q)
    (hF : ∀ f, FiniteOrderAtLeast 1 f → FiniteOrderAtLeast 1 (F f))
    {f g : FiniteWordAlgebra a s p} (hf : FiniteOrderAtLeast 1 f)
    (hg : FiniteOrderAtLeast 1 g) : F (finiteBCH f g) = finiteBCH (F f) (F g) := by
  apply finiteExp_injective_positive (hF _ (finiteBCH_order hf hg))
    (finiteBCH_order (hF f hf) (hF g hg))
  rw [← map_finiteExp F (finiteBCH_order hf hg) (hF _ (finiteBCH_order hf hg)),
    finiteExp_BCH hf hg, map_mul, map_finiteExp F hf (hF f hf),
    map_finiteExp F hg (hF g hg), finiteExp_BCH (hF f hf) (hF g hg)]

end RothschildStein.G3

-- Copyright (c) 2026 Scott Armstrong and Amélie Loher. All rights reserved.
-- Released under Apache 2.0 license as described in the file LICENSE.
module
public import Mathlib.Algebra.MvPolynomial.Monad
public import Mathlib
@[expose] public section
set_option autoImplicit false
set_option relaxedAutoImplicit false
noncomputable section
namespace RothschildStein.L1

/-- Translate polynomial variables by a fixed real vector. -/
def translatedPolynomial {N : ℕ} (P : MvPolynomial (Fin N) ℝ) (t : Fin N → ℝ) :
    MvPolynomial (Fin N) ℝ :=
  MvPolynomial.bind₁ (fun j => MvPolynomial.X j + MvPolynomial.C (t j)) P

/-- Translating coefficients preserves actual polynomial evaluation. -/
theorem translatedPolynomial_eval {N : ℕ} (P : MvPolynomial (Fin N) ℝ)
    (t ξ : Fin N → ℝ) :
    MvPolynomial.eval ξ (translatedPolynomial P t) = MvPolynomial.eval (ξ+t) P := by
  change MvPolynomial.aeval ξ (MvPolynomial.bind₁ _ P) = MvPolynomial.aeval (ξ+t) P
  rw [MvPolynomial.aeval_bind₁]
  simp only [map_add,MvPolynomial.aeval_X,MvPolynomial.aeval_C]
  rfl

/-- Translating a polynomial does not introduce any new variables,
so triangularity survives recentering (BB Theorem 10.19). -/
theorem translatedPolynomial_vars_subset {N : ℕ} (P : MvPolynomial (Fin N) ℝ)
    (t : Fin N → ℝ) : (translatedPolynomial P t).vars ⊆ P.vars := by
  classical
  intro j hj
  obtain ⟨i,hi,hji⟩ := MvPolynomial.mem_vars_bind₁ _ P hj
  have he := MvPolynomial.vars_add_subset (MvPolynomial.X i) (MvPolynomial.C (t i)) hji
  have hij : j = i := by
    simpa only [MvPolynomial.vars_X,MvPolynomial.vars_C,Finset.union_empty,Finset.mem_singleton] using he
  simpa only [hij] using hi
end RothschildStein.L1

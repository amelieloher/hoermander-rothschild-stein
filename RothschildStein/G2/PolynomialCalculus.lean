-- Copyright (c) 2026 Scott Armstrong and Amélie Loher. All rights reserved.
-- Released under Apache 2.0 license as described in the file LICENSE.
module

public import Mathlib.Algebra.MvPolynomial.PDeriv
public import Mathlib.Analysis.Calculus.ContDiff.Operations
public import Mathlib.Analysis.Calculus.FDeriv.Mul
public import Mathlib.Analysis.Calculus.FDeriv.Prod

set_option autoImplicit false
set_option relaxedAutoImplicit false
set_option backward.isDefEq.respectTransparency false

@[expose] public section
noncomputable section
namespace RothschildStein.G2
open MvPolynomial
open scoped BigOperators

/-- Polynomial evaluation in finitely many real variables is smooth. -/
theorem contDiff_eval {ι : Type*} [Fintype ι] (p : MvPolynomial ι ℝ) :
    ContDiff ℝ (⊤ : ℕ∞) (fun x : ι → ℝ => eval x p) := by
  induction p using MvPolynomial.induction_on with
  | C a => simpa using (contDiff_const (c := a))
  | add p q hp hq => simpa only [map_add] using hp.add hq
  | mul_X p j hp => simpa only [map_mul, eval_X] using hp.mul (contDiff_apply ℝ ℝ j)

/-- The differential of polynomial evaluation, written using polynomial partial derivatives. -/
def polynomialDifferential {ι : Type*} [Fintype ι] (p : MvPolynomial ι ℝ) (z : ι → ℝ) :
    (ι → ℝ) →L[ℝ] ℝ :=
  ∑ i, eval z (pderiv i p) • ContinuousLinearMap.proj i

/-- Polynomial partial derivatives compute the analytic differential. -/
theorem hasFDerivAt_eval {ι : Type*} [Fintype ι] (p : MvPolynomial ι ℝ) (z : ι → ℝ) :
    HasFDerivAt (fun x : ι → ℝ => eval x p) (polynomialDifferential p z) z := by
  classical
  induction p using MvPolynomial.induction_on with
  | C a => simpa [polynomialDifferential, pderiv_C] using (hasFDerivAt_const a z)
  | add p q hp hq =>
    convert hp.add hq using 1 <;> try rfl
    · ext x
      simp
    · ext v
      simp [polynomialDifferential, add_mul, Finset.sum_add_distrib]
  | mul_X p j hp =>
    have h := hp.mul (hasFDerivAt_apply j z)
    simp only [map_mul, eval_X]
    convert h using 1
    ext v
    simp [polynomialDifferential, pderiv_X, Pi.single_apply,
      Finset.sum_add_distrib, Finset.mul_sum, mul_add, apply_ite,
      mul_comm, mul_left_comm]

/-- Polynomial partials are the differential evaluated on a coordinate basis vector. -/
theorem fderiv_eval_single {ι : Type*} [Fintype ι] [DecidableEq ι]
    (p : MvPolynomial ι ℝ) (z : ι → ℝ) (j : ι) :
    fderiv ℝ (fun x : ι → ℝ => eval x p) z (Pi.single j 1) = eval z (pderiv j p) := by
  rw [(hasFDerivAt_eval p z).fderiv]
  simp [polynomialDifferential, Pi.single_apply]

end RothschildStein.G2

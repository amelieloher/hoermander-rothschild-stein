-- Copyright (c) 2026 Scott Armstrong and Amélie Loher. All rights reserved.
-- Released under Apache 2.0 license as described in the file LICENSE.
module

public import RothschildStein.G2.InversePolynomial
public import RothschildStein.G2.PolynomialCalculus

set_option autoImplicit false
set_option relaxedAutoImplicit false
set_option backward.isDefEq.respectTransparency false

@[expose] public section
noncomputable section
namespace RothschildStein.G2
open MvPolynomial
variable {N : ℕ} (G : HomogeneousGroup N)

/-- Polynomial inversion is smooth (BB Proposition 3.7, p. 98). -/
theorem contDiff_inv : ContDiff ℝ (⊤ : ℕ∞) G.inv :=
  contDiff_pi.mpr fun j => contDiff_eval (G.inversePolynomial j)

/-- Polynomial multiplication is smooth (BB Theorem 3.6, p. 96). -/
theorem contDiff_mul :
    ContDiff ℝ (⊤ : ℕ∞) (fun p : (Fin N → ℝ) × (Fin N → ℝ) => G.mul p.1 p.2) := by
  apply contDiff_pi.mpr
  intro k
  exact (contDiff_eval (G.productPolynomial k)).comp
    (contDiff_pi.mpr fun i => Sum.casesOn i
      (fun j => (contDiff_apply ℝ ℝ j).comp contDiff_fst)
      (fun j => (contDiff_apply ℝ ℝ j).comp contDiff_snd))

/-- The correction differential at the origin is zero
(BB Theorem 3.6(b), p. 96). -/
theorem correction_differential_zero (k : Fin N) :
    polynomialDifferential (correction G k) 0 = 0 := by
  simp only [polynomialDifferential, correction_pderiv_eval_zero, zero_smul, Finset.sum_const_zero]

/-- The inverse correction is the negative substituted product correction
(BB Proposition 3.7, p. 98). -/
theorem inverseCorrection_eval_eq (k : Fin N) (x : Fin N → ℝ) :
    eval x (inverseCorrection G k) = -eval (Sum.elim x (G.inv x)) (correction G k) := by
  have hx := inv_coordinate G x k
  rw [inv_coordinate_recursion G x k] at hx
  linarith

/-- The inverse correction has zero differential at the origin (BB Proposition 3.7, p. 98). -/
theorem inverseCorrection_hasFDerivAt_zero (k : Fin N) :
    HasFDerivAt (𝕜 := ℝ) (fun x : Fin N → ℝ => eval x (inverseCorrection G k)) 0 0 := by
  let H : (Fin N → ℝ) → (Fin N ⊕ Fin N) → ℝ := fun x => Sum.elim x (G.inv x)
  have hH : ContDiff ℝ (⊤ : ℕ∞) H :=
    contDiff_pi.mpr fun i => Sum.casesOn i
      (fun j => contDiff_apply ℝ ℝ j)
      (fun j => contDiff_eval (G.inversePolynomial j))
  have hH0 : H 0 = 0 := by ext i; cases i <;> simp [H, inv_zero]
  have hQ := hasFDerivAt_eval (correction G k) (0 : (Fin N ⊕ Fin N) → ℝ)
  rw [correction_differential_zero] at hQ
  have hQ' : HasFDerivAt (𝕜 := ℝ) (fun z => eval z (correction G k)) 0 (H 0) := by
    simpa only [hH0] using hQ
  have hc := hQ'.comp 0 ((hH.differentiable (by simp)).differentiableAt.hasFDerivAt)
  have he : (fun x => eval x (inverseCorrection G k)) =
      -(fun x => eval (H x) (correction G k)) := by
    funext x
    exact inverseCorrection_eval_eq G k x
  rw [he]
  convert hc.neg using 1 <;> try rfl
  simp

/-- The analytic differential of inversion at the identity is −Id
(BB Proposition 3.7, p. 98). -/
theorem inv_hasFDerivAt_zero :
    HasFDerivAt G.inv (-ContinuousLinearMap.id ℝ (Fin N → ℝ)) 0 := by
  apply hasFDerivAt_pi'.mpr
  intro k
  have h := (hasFDerivAt_apply (𝕜 := ℝ) k (0 : Fin N → ℝ)).neg.add
    (inverseCorrection_hasFDerivAt_zero G k)
  have he : (fun x => G.inv x k) = (fun x => -x k + eval x (inverseCorrection G k)) :=
    funext fun x => inv_coordinate G x k
  rw [he]
  convert h using 1; try rfl
  ext x
  simp

end RothschildStein.G2

-- Copyright (c) 2026 Scott Armstrong and Amélie Loher. All rights reserved.
-- Released under Apache 2.0 license as described in the file LICENSE.
module

public import RothschildStein.G2.InvariantBasis
public import Mathlib.RingTheory.MvPolynomial.EulerIdentity

set_option autoImplicit false
set_option relaxedAutoImplicit false
set_option backward.isDefEq.respectTransparency false

@[expose] public section
noncomputable section
namespace RothschildStein.G2
open MvPolynomial
open scoped BigOperators
variable {N : ℕ} (G : HomogeneousGroup N)

/-- Polynomial coefficients of the canonical left-invariant fields
(BB Theorem 3.29, pp. 110–111). -/
def leftCoefficient (i k : Fin N) : MvPolynomial (Fin N) ℝ :=
  (pderiv (Sum.inr i) (G.productPolynomial k)).killCompl Sum.inl_injective

/-- Polynomial coefficients of the canonical right-invariant fields (BB p. 111). -/
def rightCoefficient (i k : Fin N) : MvPolynomial (Fin N) ℝ :=
  (pderiv (Sum.inl i) (G.productPolynomial k)).killCompl Sum.inr_injective

private theorem killCompl_X_image {α β : Type*} (f : α → β) (hf : Function.Injective f)
    (j : α) : (killCompl (R := ℝ) hf) (X (f j)) = X j := by
  rw [← rename_X f, killCompl_rename_app]

private theorem killCompl_X_outside {α β : Type*} (f : α → β) (hf : Function.Injective f)
    (j : β) (hj : j ∉ Set.range f) : (killCompl (R := ℝ) hf) (X j) = 0 := by
  simp [killCompl, hj]

/-- Specializing the second block of variables to zero. -/
theorem eval_killCompl_inl (p : MvPolynomial (Fin N ⊕ Fin N) ℝ) (x : Fin N → ℝ) :
    eval x (p.killCompl Sum.inl_injective) = eval (Sum.elim x 0) p := by
  have h : (eval x).comp (killCompl (R := ℝ)
      (f := (Sum.inl : Fin N → Fin N ⊕ Fin N)) Sum.inl_injective).toRingHom =
      eval (Sum.elim x 0) := by
    apply ringHom_ext
    · intro r; simp
    · intro j
      cases j with
      | inl j => simp [killCompl_X_image]
      | inr j => simp [killCompl_X_outside, Set.mem_range]
  exact RingHom.congr_fun h p

/-- Specializing the first block of variables to zero. -/
theorem eval_killCompl_inr (p : MvPolynomial (Fin N ⊕ Fin N) ℝ) (x : Fin N → ℝ) :
    eval x (p.killCompl Sum.inr_injective) = eval (Sum.elim 0 x) p := by
  have h : (eval x).comp (killCompl (R := ℝ)
      (f := (Sum.inr : Fin N → Fin N ⊕ Fin N)) Sum.inr_injective).toRingHom =
      eval (Sum.elim 0 x) := by
    apply ringHom_ext
    · intro r; simp
    · intro j
      cases j with
      | inl j => simp [killCompl_X_outside, Set.mem_range]
      | inr j => simp [killCompl_X_image]
  exact RingHom.congr_fun h p

private theorem left_coordinate_derivative (x : Fin N → ℝ) (k : Fin N) :
    HasFDerivAt (fun y => G.mul x y k)
      ((polynomialDifferential (G.productPolynomial k) (Sum.elim x 0)).comp
        (ContinuousLinearMap.pi fun i => Sum.casesOn i
          (fun _ => 0) (fun j => (ContinuousLinearMap.proj j : (Fin N → ℝ) →L[ℝ] ℝ)))) 0 := by
  have hH : HasFDerivAt (fun y : Fin N → ℝ => Sum.elim x y)
      (ContinuousLinearMap.pi fun i : Fin N ⊕ Fin N => Sum.casesOn i
        (fun _ => 0) (fun j => (ContinuousLinearMap.proj j : (Fin N → ℝ) →L[ℝ] ℝ))) 0 := by
    apply hasFDerivAt_pi.mpr
    intro i
    cases i with
    | inl j => exact hasFDerivAt_const _ _
    | inr j => exact hasFDerivAt_apply j 0
  exact (hasFDerivAt_eval (G.productPolynomial k) (Sum.elim x 0)).comp 0 hH

private theorem right_coordinate_derivative (x : Fin N → ℝ) (k : Fin N) :
    HasFDerivAt (fun y => G.mul y x k)
      ((polynomialDifferential (G.productPolynomial k) (Sum.elim 0 x)).comp
        (ContinuousLinearMap.pi fun i => Sum.casesOn i
          (fun j => (ContinuousLinearMap.proj j : (Fin N → ℝ) →L[ℝ] ℝ)) (fun _ => 0))) 0 := by
  have hH : HasFDerivAt (fun y : Fin N → ℝ => Sum.elim y x)
      (ContinuousLinearMap.pi fun i : Fin N ⊕ Fin N => Sum.casesOn i
        (fun j => (ContinuousLinearMap.proj j : (Fin N → ℝ) →L[ℝ] ℝ)) (fun _ => 0)) 0 := by
    apply hasFDerivAt_pi.mpr
    intro i
    cases i with
    | inl j => exact hasFDerivAt_apply j 0
    | inr j => exact hasFDerivAt_const _ _
  exact (hasFDerivAt_eval (G.productPolynomial k) (Sum.elim 0 x)).comp 0 hH

/-- The canonical field has the polynomial coefficients of BB (3.11), p. 110. -/
theorem canonicalField_coordinate (i k : Fin N) (x : Fin N → ℝ) :
    G.canonicalField i x k = eval x (leftCoefficient G i k) := by
  have h := hasFDerivAt_pi.mpr (left_coordinate_derivative G x)
  rw [HomogeneousGroup.canonicalField, h.fderiv]
  simp [leftCoefficient, eval_killCompl_inl, polynomialDifferential,
    Hormander.Interface.basisVec, Pi.single_apply, Fintype.sum_sum_type]

/-- The corresponding coordinate formula for the right-invariant fields (BB p. 111). -/
theorem rightField_coordinate (i k : Fin N) (x : Fin N → ℝ) :
    rightField G (Hormander.Interface.basisVec i) x k = eval x (rightCoefficient G i k) := by
  have h := hasFDerivAt_pi.mpr (right_coordinate_derivative G x)
  rw [rightField, h.fderiv]
  simp [rightCoefficient, eval_killCompl_inr, polynomialDifferential,
    Hormander.Interface.basisVec, Pi.single_apply, Fintype.sum_sum_type]

/-- The coefficient matrix of the left canonical basis is unit upper triangular
(BB Theorem 3.29, p. 110). -/
theorem leftCoefficient_of_le (i k : Fin N) (hki : k ≤ i) :
    leftCoefficient G i k = if i = k then 1 else 0 := by
  simp [leftCoefficient, product_pderiv_inr G k i hki]

end RothschildStein.G2

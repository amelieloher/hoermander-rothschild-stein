-- Copyright (c) 2026 Scott Armstrong and Amélie Loher. All rights reserved.
-- Released under Apache 2.0 license as described in the file LICENSE.
module

public import RothschildStein.G2.DifferentialTranspose
public import Mathlib.Analysis.Calculus.FDeriv.Add

set_option autoImplicit false
set_option relaxedAutoImplicit false
set_option backward.isDefEq.respectTransparency false
@[expose] public section
noncomputable section
namespace RothschildStein.H1
variable {N : ℕ}

private theorem coordinateFold_const_mul (l : List (Fin N)) (c : ℝ)
    (f : (Fin N → ℝ) → ℝ) :
    l.foldr (fun j h x => fderiv ℝ h x (Hormander.Interface.basisVec j)) (fun x => c * f x) =
      fun x => c * l.foldr (fun j h y => fderiv ℝ h y (Hormander.Interface.basisVec j)) f x := by
  induction l with
  | nil => rfl
  | cons j l ih =>
    simp only [List.foldr_cons, ih]
    funext x
    change fderiv ℝ (c • l.foldr (fun j h y => fderiv ℝ h y (Hormander.Interface.basisVec j)) f)
      x (Hormander.Interface.basisVec j) = _
    rw [fderiv_const_smul_field]
    rfl

/-- Multi-index differentiation commutes with a scalar
without imposing global smoothness on a punctured kernel. -/
theorem euclideanPartial_const_mul (a : Fin N → ℕ) (c : ℝ)
    (f : (Fin N → ℝ) → ℝ) :
    euclideanPartial a (fun x => c * f x) = fun x => c * euclideanPartial a f x :=
  coordinateFold_const_mul _ c f

/-- The differential operator commutes with scalar multiplication. -/
theorem differentialOperator_const_mul (P : SmoothDifferentialOperator N) (c : ℝ)
    (f : (Fin N → ℝ) → ℝ) :
    P.apply (fun x => c * f x) = fun x => c * P.apply f x := by
  funext x
  simp only [SmoothDifferentialOperator.apply, euclideanPartial_const_mul, Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro a _
  ring

/-- The formal transpose commutes with scalar multiplication. -/
theorem differentialTranspose_const_mul (P : SmoothDifferentialOperator N) (c : ℝ)
    (f : (Fin N → ℝ) → ℝ) :
    G2.differentialTranspose P (fun x => c * f x) = fun x => c * G2.differentialTranspose P f x := by
  funext x
  simp only [G2.differentialTranspose, Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro a _
  have he : (fun y => P.coefficient a y * (c * f y)) =
      fun y => c * (P.coefficient a y * f y) := by funext y; ring
  rw [he, euclideanPartial_const_mul]
  ring

end RothschildStein.H1

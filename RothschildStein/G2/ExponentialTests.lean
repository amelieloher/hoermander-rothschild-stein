-- Copyright (c) 2026 Scott Armstrong and Amélie Loher. All rights reserved.
-- Released under Apache 2.0 license as described in the file LICENSE.
module

public import RothschildStein.G2.CoordinateWords
public import Mathlib.Analysis.SpecialFunctions.ExpDeriv
public import Mathlib.Algebra.BigOperators.Group.List.Basic
public import Mathlib.Algebra.BigOperators.Fin

set_option autoImplicit false
set_option relaxedAutoImplicit false
set_option backward.isDefEq.respectTransparency false
@[expose] public section
noncomputable section
open scoped BigOperators
namespace RothschildStein.G2
variable {N : ℕ}

/-- Linear exponent used to distinguish finite differential coefficients. -/
def linearExponent (z : Fin N → ℝ) : (Fin N → ℝ) →L[ℝ] ℝ :=
  ∑ j, z j • ContinuousLinearMap.proj j

/-- Evaluation of the linear exponent on a coordinate vector. -/
theorem linearExponent_basis (z : Fin N → ℝ) (j : Fin N) :
    linearExponent z (Hormander.Interface.basisVec j) = z j := by
  classical
  simp [linearExponent, Hormander.Interface.basisVec, Pi.single_apply]

/-- The smooth exponential test for a finite differential operator. -/
def exponentialTest (z : Fin N → ℝ) (x : Fin N → ℝ) : ℝ := Real.exp (linearExponent z x)

/-- Exponential tests are globally smooth. -/
theorem exponentialTest_smooth (z : Fin N → ℝ) :
    ContDiff ℝ (⊤ : ℕ∞) (exponentialTest z) :=
  (linearExponent z).contDiff.exp

/-- A coordinate word acts diagonally on an exponential test. -/
theorem coordinateWord_exponential (l : List (Fin N)) (z : Fin N → ℝ) :
    l.foldr (fun j g x => fderiv ℝ g x (Hormander.Interface.basisVec j))
      (exponentialTest z) = fun x => (l.map z).prod * exponentialTest z x := by
  induction l with
  | nil => simp
  | cons j l ih =>
    rw [List.foldr_cons, ih]
    funext x
    have hd := (((linearExponent z).hasFDerivAt (x := x)).exp.const_mul (l.map z).prod).fderiv
    change fderiv ℝ (fun y => (l.map z).prod * Real.exp (linearExponent z y)) x _ = _
    rw [hd]
    simp only [smul_apply, smul_eq_mul, linearExponent_basis,
      List.map_cons, List.prod_cons, exponentialTest]
    ring

/-- Grouping a coordinate word gives the multi-index monomial. -/
theorem coordinateWord_product (a : Fin N → ℕ) (z : Fin N → ℝ) :
    ((coordinateWord a).map z).prod = ∏ j, z j ^ a j := by
  classical
  have h (l : List (Fin N)) :
      ((l.flatMap fun j => List.replicate (a j) j).map z).prod =
        (l.map fun j => z j ^ a j).prod := by
    induction l with
    | nil => simp
    | cons j l ih => simp [List.flatMap_cons, List.map_append, ih]
  rw [coordinateWord, h, ← Fin.prod_univ_def]

/-- Exact derivatives of the
exponential tests (BB Definition 3.22, p. 106). -/
theorem euclideanPartial_exponential (a : Fin N → ℕ) (z x : Fin N → ℝ) :
    euclideanPartial a (exponentialTest z) x = (∏ j, z j ^ a j) * exponentialTest z x := by
  change ((coordinateWord a).foldr _ (exponentialTest z)) x = _
  rw [coordinateWord_exponential, coordinateWord_product]

end RothschildStein.G2

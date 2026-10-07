-- Copyright (c) 2026 Scott Armstrong and Amélie Loher. All rights reserved.
-- Released under Apache 2.0 license as described in the file LICENSE.
module

public import Hormander.B.Extension.Conjugation
public import Hormander.B.Mollifier.CutoffAlgebra

@[expose] public section

noncomputable section

open MeasureTheory SchwartzMap
open scoped ComplexConjugate

namespace Hormander.C

open Hormander.B

variable {N : ℕ}

/-- The real Schwartz function `-div X = -∑ᵢ ∂ᵢ Xⁱ`. -/
def negDiv (X : RealSchwartzVectorField N) : SchwartzMap (Carrier N) ℝ :=
  -∑ i : Fin N, LineDeriv.lineDerivOp (EuclideanSpace.single i (1 : ℝ)) (X i)

theorem negDiv_apply (X : RealSchwartzVectorField N) (x : Carrier N) :
    negDiv X x = -∑ i : Fin N, fderiv ℝ (X i) x (EuclideanSpace.single i (1 : ℝ)) := by
  unfold negDiv
  simp only [neg_apply, sum_apply]
  congr 1

theorem complexify_deriv (a : SchwartzMap (Carrier N) ℝ) (i : Fin N) (x : Carrier N) :
    coordinateDerivative i (complexifyRealSchwartz a) x =
      ((fderiv ℝ a x (EuclideanSpace.single i (1 : ℝ)) : ℝ) : ℂ) := by
  have h1 : coordinateDerivative i (complexifyRealSchwartz a) x =
      fderiv ℝ (complexifyRealSchwartz a) x (EuclideanSpace.single i (1 : ℝ)) :=
    SchwartzMap.lineDerivOp_apply_eq_fderiv _ _ x
  rw [h1]
  have hd : HasFDerivAt (fun y => ((a y : ℝ) : ℂ))
      (Complex.ofRealCLM.comp (fderiv ℝ a x)) x :=
    Complex.ofRealCLM.hasFDerivAt.comp x (a.differentiableAt.hasFDerivAt)
  have : (⇑(complexifyRealSchwartz a) : Carrier N → ℂ) = fun y => ((a y : ℝ) : ℂ) := by
    funext y; exact complexifyRealSchwartz_apply a y
  rw [this, hd.fderiv]
  simp

theorem complexify_negDiv (X : RealSchwartzVectorField N) (x : Carrier N) :
    complexifyRealSchwartz (negDiv X) x =
      -∑ i : Fin N, coordinateDerivative i (complexifyRealSchwartz (X i)) x := by
  rw [complexifyRealSchwartz_apply, negDiv_apply]
  push_cast
  congr 1
  refine Finset.sum_congr rfl fun i _ => ?_
  rw [complexify_deriv]

/-- Per-coordinate integration by parts for `M_a ∂ᵢ`. -/
theorem integral_DOp_mul (a u w : TestFunction N) (i : Fin N) :
    ∫ x, (multiplierOperator a (coordinateDerivative i u)) x * w x =
      -∫ x, u x * (coordinateDerivative i a x * w x + a x * coordinateDerivative i w x) := by
  have h := SchwartzMap.integral_mul_lineDerivOp_right_eq_neg_left (μ := volume)
    (multiplierOperator a w) u (EuclideanSpace.single i (1 : ℝ))
  have h2 : ∀ x, (multiplierOperator a (coordinateDerivative i u)) x * w x =
      (coordinateDerivative i u x) * (multiplierOperator a w x) := fun x => by
    rw [multiplierOperator_apply, multiplierOperator_apply]; ring
  simp_rw [h2]
  have e1 : ∫ x, coordinateDerivative i u x * multiplierOperator a w x =
      ∫ x, multiplierOperator a w x * coordinateDerivative i u x := by
    congr 1; funext x; ring
  rw [e1]
  have := h
  change ∫ x, multiplierOperator a w x * coordinateDerivative i u x =
    -∫ x, coordinateDerivative i (multiplierOperator a w) x * u x at this
  rw [this]
  congr 2
  funext x
  rw [coordinateDerivative_mul_apply]
  ring


/-- Bilinear integration by parts for a real Schwartz vector field:
`∫ (X u) w = ∫ u (-X w + (-div X) w)`. -/
theorem integral_vectorField_mul (X : RealSchwartzVectorField N) (u w : TestFunction N) :
    ∫ x, vectorFieldOperator X u x * w x =
      ∫ x, u x * (-(vectorFieldOperator X w x) + (negDiv X x : ℂ) * w x) := by
  set a : Fin N → TestFunction N := fun i => complexifyRealSchwartz (X i) with ha
  set S : Fin N → TestFunction N := fun i =>
    multiplierOperator (coordinateDerivative i (a i)) w +
      multiplierOperator (a i) (coordinateDerivative i w) with hS
  have hV : ∀ (v : TestFunction N) x, vectorFieldOperator X v x =
      ∑ i : Fin N, multiplierOperator (a i) (coordinateDerivative i v) x := fun v x => by
    unfold vectorFieldOperator
    rw [LinearMap.sum_apply, sum_apply]
    rfl
  have h1 : ∀ x, vectorFieldOperator X u x * w x =
      ∑ i : Fin N, multiplierOperator (a i) (coordinateDerivative i u) x * w x := fun x => by
    rw [hV, Finset.sum_mul]
  simp_rw [h1]
  rw [integral_finsetSum _ (fun i _ => integrable_mul_test _ w)]
  have h2 : ∀ i, ∫ x, multiplierOperator (a i) (coordinateDerivative i u) x * w x =
      -∫ x, u x * S i x := fun i => by
    rw [integral_DOp_mul]
    congr 2; funext x
    simp only [hS, add_apply, multiplierOperator_apply]
  simp_rw [h2]
  rw [Finset.sum_neg_distrib, ← integral_finsetSum _ (fun i _ => integrable_mul_test u (S i)),
    ← integral_neg]
  congr 1; funext x
  rw [← Finset.mul_sum]
  have hsum : ∑ i : Fin N, S i x = vectorFieldOperator X w x - (negDiv X x : ℂ) * w x := by
    simp only [hS, add_apply, multiplierOperator_apply]
    rw [Finset.sum_add_distrib, ← Finset.sum_mul, hV w x]
    simp only [multiplierOperator_apply]
    have : (negDiv X x : ℂ) = complexifyRealSchwartz (negDiv X) x :=
      (complexifyRealSchwartz_apply _ x).symm
    rw [this, complexify_negDiv]
    simp only [ha]
    ring
  rw [hsum]
  ring


theorem vectorField_conjTest (X : RealSchwartzVectorField N) (v : TestFunction N) :
    vectorFieldOperator X (conjTest v) = conjTest (vectorFieldOperator X v) := by
  have h := LinearMap.congr_fun (conjOperator_vectorField X) (conjTest v)
  rw [conjOperator_apply, conjTest_conjTest] at h
  exact h.symm

/-- The Hermitian adjoint of a real Schwartz vector field is `X* = -X + (-div X)`. -/
theorem vectorField_hasHermitianAdjoint (X : RealSchwartzVectorField N) :
    HasHermitianAdjoint (vectorFieldOperator X)
      (-(vectorFieldOperator X) + realMultiplierOperator (negDiv X)) := by
  intro u v
  unfold hermitianPairing
  have h := integral_vectorField_mul X u (conjTest v)
  have e : ∀ x, vectorFieldOperator X u x * conj (v x) = vectorFieldOperator X u x * conjTest v x :=
    fun x => by simp
  simp_rw [e]
  rw [h]
  congr 1; funext x
  rw [vectorField_conjTest]
  have hg : realMultiplierOperator (negDiv X) v x = (negDiv X x : ℂ) * v x := by
    unfold realMultiplierOperator
    rw [multiplierOperator_apply, complexifyRealSchwartz_apply]
  simp only [LinearMap.add_apply, LinearMap.neg_apply, add_apply, neg_apply, conjTest_apply, hg,
    map_add, map_neg, map_mul, Complex.conj_ofReal]

end Hormander.C

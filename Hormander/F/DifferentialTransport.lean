-- Copyright (c) 2026 Scott Armstrong and Amélie Loher. All rights reserved.
-- Released under Apache 2.0 license as described in the file LICENSE.
module

public import Hormander.F.Coordinates
public import Hormander.Interface.EuclideanDivergence
public import Hormander.Interface.LieWordEval
public import Mathlib.Analysis.Calculus.FDeriv.Basic
public import Mathlib.Analysis.Calculus.VectorField

@[expose] public section

noncomputable section

open Hormander.Interface
open scoped BigOperators

namespace Hormander.F

/-- Fréchet derivatives conjugate under the fixed coordinate
equivalence, including at points where the function is not differentiable (where both total
derivatives are zero). -/
theorem fderiv_coordinateConjugate {N : ℕ} (f : (Fin N → ℝ) → (Fin N → ℝ))
    (x : Fin N → ℝ) :
    fderiv ℝ (fun y : E₂ N => coordinateEquiv N (f ((coordinateEquiv N).symm y)))
        (coordinateEquiv N x) =
      (coordinateEquiv N : (Fin N → ℝ) →L[ℝ] E₂ N).comp
        ((fderiv ℝ f x).comp ((coordinateEquiv N).symm : E₂ N →L[ℝ] (Fin N → ℝ))) := by
  let e := coordinateEquiv N
  by_cases hf : DifferentiableAt ℝ f x
  · have hbase : e.symm (e x) = x := e.symm_apply_apply x
    have hfd : HasFDerivAt f (fderiv ℝ f x) (e.symm (e x)) := by
      rw [hbase]
      exact hf.hasFDerivAt
    have hcomp := hfd.comp_semilinear (e : (Fin N → ℝ) →L[ℝ] E₂ N)
      (e.symm : E₂ N →L[ℝ] (Fin N → ℝ))
    simpa [e, Function.comp_def] using hcomp.fderiv
  · have hnot : ¬DifferentiableAt ℝ
        (fun y : E₂ N => e (f (e.symm y))) (e x) := by
      intro hh
      have hinv := hh.comp_semilinear₂
        (e.symm : E₂ N →L[ℝ] (Fin N → ℝ))
        (e : (Fin N → ℝ) →L[ℝ] E₂ N)
      apply hf
      simpa [e, coordinateEquiv, Function.comp_def,
        PiLp.coe_symm_continuousLinearEquiv, PiLp.coe_continuousLinearEquiv] using hinv
    rw [fderiv_zero_of_not_differentiableAt hf,
      fderiv_zero_of_not_differentiableAt hnot]
    simp

/-- Push a vector field on `Fin N → ℝ` to the Euclidean carrier. -/
def pushVectorField {N : ℕ} (V : (Fin N → ℝ) → (Fin N → ℝ)) : E₂ N → E₂ N :=
  fun y => coordinateEquiv N (V ((coordinateEquiv N).symm y))

/-- The global vector-field bracket is preserved by the
coordinate equivalence, without smoothness assumptions because `fderiv` is totalized by zero. -/
theorem lieBracket_coordinateConjugate {N : ℕ} (V W : (Fin N → ℝ) → (Fin N → ℝ))
    (x : Fin N → ℝ) :
    coordinateEquiv N (VectorField.lieBracket ℝ V W x) =
      VectorField.lieBracket ℝ (pushVectorField V) (pushVectorField W)
        (coordinateEquiv N x) := by
  have hWV : fderiv ℝ (pushVectorField W) (coordinateEquiv N x)
      (pushVectorField V (coordinateEquiv N x)) =
      coordinateEquiv N (fderiv ℝ W x (V x)) := by
    change fderiv ℝ (fun y : E₂ N => coordinateEquiv N (W ((coordinateEquiv N).symm y)))
      (coordinateEquiv N x) (coordinateEquiv N (V x)) = _
    rw [fderiv_coordinateConjugate]
    simp
  have hVW : fderiv ℝ (pushVectorField V) (coordinateEquiv N x)
      (pushVectorField W (coordinateEquiv N x)) =
      coordinateEquiv N (fderiv ℝ V x (W x)) := by
    change fderiv ℝ (fun y : E₂ N => coordinateEquiv N (V ((coordinateEquiv N).symm y)))
      (coordinateEquiv N x) (coordinateEquiv N (W x)) = _
    rw [fderiv_coordinateConjugate]
    simp
  rw [VectorField.lieBracket, VectorField.lieBracket, hWV, hVW]
  simp

/-- The Euclidean coordinate trace of the derivative of a vector field. -/
def euclideanDivergence₂ {N : ℕ} (V : E₂ N → E₂ N) (x : E₂ N) : ℝ :=
  ∑ i : Fin N, (fderiv ℝ V x (EuclideanSpace.single i (1 : ℝ))) i

/-- The coordinate map sends the standard basis `Hormander.Interface.basisVec` to the Euclidean
coordinate basis. -/
theorem coordinateEquiv_basisVec {N : ℕ} (i : Fin N) :
    coordinateEquiv N (Hormander.Interface.basisVec i) =
      EuclideanSpace.single i (1 : ℝ) := by
  simp [coordinateEquiv, Hormander.Interface.basisVec]

/-- The coordinate trace defining the divergence on `Fin N → ℝ` is the
Euclidean coordinate trace after transporting a vector field. -/
theorem euclideanDivergence_coordinateConjugate {N : ℕ}
    (V : (Fin N → ℝ) → (Fin N → ℝ)) (x : Fin N → ℝ) :
    euclideanDivergence₂ (pushVectorField V) (coordinateEquiv N x) =
      Hormander.Interface.euclideanDivergence V x := by
  unfold euclideanDivergence₂ Hormander.Interface.euclideanDivergence
  change ∑ i : Fin N,
      (fderiv ℝ (fun y : E₂ N => coordinateEquiv N (V ((coordinateEquiv N).symm y)))
        (coordinateEquiv N x) (EuclideanSpace.single i (1 : ℝ))) i =
    ∑ i : Fin N, (fderiv ℝ V x (Hormander.Interface.basisVec i)) i
  apply Finset.sum_congr rfl
  intro i hi
  have hderiv := fderiv_coordinateConjugate (N := N) V x
  have hcoordinate := congrArg
    (fun A : E₂ N →L[ℝ] E₂ N => (A (EuclideanSpace.single i (1 : ℝ))) i) hderiv
  simpa [coordinateEquiv_basisVec, Hormander.Interface.basisVec] using hcoordinate

/-- Push every field in a family to the Euclidean carrier. -/
def pushVectorFields {k N : ℕ} (X : Fin (k + 1) → (Fin N → ℝ) → (Fin N → ℝ)) :
    Fin (k + 1) → E₂ N → E₂ N :=
  fun i => pushVectorField (X i)

/-- Recursive Lie-word evaluation commutes with the
coordinate transfer. -/
theorem lieWordEval_coordinateConjugate {k N : ℕ}
    (X : Fin (k + 1) → (Fin N → ℝ) → (Fin N → ℝ)) (w : LieWord k) :
    Hormander.lieWordEval (pushVectorFields X) w =
      fun y => coordinateEquiv N (Hormander.Interface.LieWord.eval X w
        ((coordinateEquiv N).symm y)) := by
  induction w with
  | generator i =>
      rfl
  | bracket p q hp hq =>
      funext y
      change VectorField.lieBracket ℝ (Hormander.lieWordEval (pushVectorFields X) p)
        (Hormander.lieWordEval (pushVectorFields X) q) y = _
      rw [hp, hq]
      change VectorField.lieBracket ℝ
          (pushVectorField (Hormander.Interface.LieWord.eval X p))
          (pushVectorField (Hormander.Interface.LieWord.eval X q)) y = _
      simpa only [coordinateEquiv_apply_symm_apply, Hormander.Interface.LieWord.eval] using
        (lieBracket_coordinateConjugate
          (V := Hormander.Interface.LieWord.eval X p)
          (W := Hormander.Interface.LieWord.eval X q)
          ((coordinateEquiv N).symm y)).symm

end Hormander.F

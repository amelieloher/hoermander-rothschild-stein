-- Copyright (c) 2026 Scott Armstrong and Amélie Loher. All rights reserved.
-- Released under Apache 2.0 license as described in the file LICENSE.
module

public import Mathlib
public import RothschildStein.G3.WordPolynomials
public import RothschildStein.G3.RationalLieAlgebras

set_option autoImplicit false
set_option relaxedAutoImplicit false
@[expose] public section
noncomputable section
open scoped BigOperators
namespace RothschildStein.G3

/-- Rational free associative polynomials embed
in the existing real coefficient completion (BB pp. 467–469). -/
def mathlibCoefficients (a : ℕ) : FreeAlgebra ℚ (Fin a) →ₐ[ℚ] CoefficientSeries a :=
  (((polynomialSeries a).toRingHom.comp
    (MonoidAlgebra.mapRingHom (FreeMonoid (Fin a)) (algebraMap ℚ ℝ))).comp
      (FreeAlgebra.equivMonoidAlgebraFreeMonoid.toRingHom)).toRatAlgHom

/-- The map preserves each rational word coefficient
under the injective rational-to-real cast (BB p. 467). -/
theorem mathlibCoefficients_apply {a : ℕ} (f : FreeAlgebra ℚ (Fin a)) (I : List (Fin a)) :
    mathlibCoefficients a f I =
      ((FreeAlgebra.equivMonoidAlgebraFreeMonoid f).coeff (FreeMonoid.ofList I) : ℝ) := by
  change polynomialSeries a (MonoidAlgebra.mapRingHom (FreeMonoid (Fin a))
    (algebraMap ℚ ℝ) (FreeAlgebra.equivMonoidAlgebraFreeMonoid f)) I = _
  rw [polynomialSeries_coeff,MonoidAlgebra.coeff_mapRingHom]
  rfl

/-- Rational free polynomials are determined by
 their coefficient series (BB pp. 467–468). -/
theorem mathlibCoefficients_injective (a : ℕ) : Function.Injective (mathlibCoefficients a) := by
  intro f g h
  apply FreeAlgebra.equivMonoidAlgebraFreeMonoid.injective
  ext I
  apply Rat.cast_injective (α := ℝ)
  have he := congrFun h I.toList
  simpa only [mathlibCoefficients_apply,FreeMonoid.ofList_toList] using he

/-- The free generators map to the existing
letter coefficient series (BB p. 467). -/
@[simp] theorem mathlibCoefficients_generator {a : ℕ} (i : Fin a) :
    mathlibCoefficients a (FreeAlgebra.ι ℚ i) = letterSeries i := by
  change polynomialSeries a (MonoidAlgebra.mapRingHom (FreeMonoid (Fin a))
    (algebraMap ℚ ℝ) (FreeAlgebra.equivMonoidAlgebraFreeMonoid (FreeAlgebra.ι ℚ i))) = _
  simp only [FreeAlgebra.equivMonoidAlgebraFreeMonoid,AlgEquiv.ofAlgHom_apply,
    FreeAlgebra.lift_ι_apply,MonoidAlgebra.of_apply,MonoidAlgebra.mapRingHom_single,
    map_one,polynomialSeries_single,one_smul]
  rfl

/-- The finite coefficient map is rational algebraic
truncation of the completed coefficient map (BB pp. 468–469). -/
def mathlibTruncation (a N : ℕ) :
    FreeAlgebra ℚ (Fin a) →ₐ[ℚ] FiniteWordAlgebra a N (fun _ => 1) :=
  ((truncateSeries (a := a) (s := N) (p := fun _ => 1)).restrictScalars ℚ).comp
    (mathlibCoefficients a)

end RothschildStein.G3

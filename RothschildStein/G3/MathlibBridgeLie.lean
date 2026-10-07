-- Copyright (c) 2026 Scott Armstrong and Amélie Loher. All rights reserved.
-- Released under Apache 2.0 license as described in the file LICENSE.
module

public import RothschildStein.G3.MathlibBridgeWords
public import RothschildStein.G3.HomogeneousLiePolynomials

set_option autoImplicit false
set_option relaxedAutoImplicit false
@[expose] public section
noncomputable section
namespace RothschildStein.G3
variable {a : ℕ}

local instance mathlibBridgeAssociativeLieRing : LieRing (FreeAlgebra ℚ (Fin a)) :=
  LieRing.ofAssociativeRing

/-- The canonical free Lie image in the rational
free associative algebra, viewed as a linear map (BB pp. 469–472). -/
def mathlibLieImage (a : ℕ) : FreeLieAlgebra ℚ (Fin a) →ₗ[ℚ] FreeAlgebra ℚ (Fin a) :=
  (FreeLieAlgebra.lift ℚ (FreeAlgebra.ι ℚ : Fin a → FreeAlgebra ℚ (Fin a))).toLinearMap

/-- This image is exactly the universal-envelope
spelling fixed in the fixed root (BB pp. 469–472). -/
theorem mathlibLieImage_canonical (z : FreeLieAlgebra ℚ (Fin a)) :
    mathlibLieImage a z = FreeLieAlgebra.universalEnvelopingEquivFreeAlgebra ℚ (Fin a)
      (UniversalEnvelopingAlgebra.ι ℚ z) := by
  simp [mathlibLieImage]

/-- Canonical generators retain their labels
(BB p. 469). -/
@[simp] theorem mathlibLieImage_generator (i : Fin a) :
    mathlibLieImage a (FreeLieAlgebra.of ℚ i) = FreeAlgebra.ι ℚ i := by
  simp [mathlibLieImage]

/-- The canonical bracket has the positive
associative commutator sign required by exp(x) exp(y) (BB pp. 470–471). -/
@[simp] theorem mathlibLieImage_bracket (u v : FreeLieAlgebra ℚ (Fin a)) :
    mathlibLieImage a ⁅u,v⁆ = mathlibLieImage a u * mathlibLieImage a v -
      mathlibLieImage a v * mathlibLieImage a u := by
  simp [mathlibLieImage,LieRing.of_associative_ring_bracket]

/-- Homogeneous Lie polynomials are the rational
span of n-leaf right-nested free brackets (BB Lemma 9.70, pp. 471–472). -/
def mathlibHomogeneousLieSpan (a n : ℕ) : Submodule ℚ (FreeLieAlgebra ℚ (Fin a)) :=
  Submodule.span ℚ {z | ∃ u : Nested (Fin a),u.letters.length = n ∧
    z = u.eval (FreeLieAlgebra.of ℚ)}

/-- Each nested free bracket maps to exactly
its existing coefficient-series evaluation (BB pp. 469–472). -/
theorem mathlibCoefficients_nested (u : Nested (Fin a)) :
    mathlibCoefficients a (mathlibLieImage a (u.eval (FreeLieAlgebra.of ℚ))) =
      u.eval letterSeries := by
  induction u with
  | letter i => simp [Nested.eval]
  | bracket i u ih =>
    simp only [Nested.eval,mathlibLieImage_bracket,mathlibLieImage_generator,
      map_sub,map_mul,mathlibCoefficients_generator,ih]
    rfl

/-- A rational homogeneous coefficient Lie
polynomial has a lift in the corresponding free Lie span. This is
existence of a lift, without any PBW or Lie-level uniqueness assumption
(BB Lemma 9.70, pp. 471–474). -/
theorem exists_mathlib_homogeneous_lie_lift {n : ℕ} {f : CoefficientSeries a}
    (hf : f ∈ homogeneousRationalLieSpan a n) :
    ∃ z ∈ mathlibHomogeneousLieSpan a n,
      mathlibCoefficients a (mathlibLieImage a z) = f := by
  induction hf using Submodule.span_induction with
  | mem f hf =>
    obtain ⟨u,hu,rfl⟩ := hf
    exact ⟨u.eval (FreeLieAlgebra.of ℚ),Submodule.subset_span ⟨u,hu,rfl⟩,
      mathlibCoefficients_nested u⟩
  | zero => exact ⟨0,Submodule.zero_mem _,by simp⟩
  | add f g _ _ hf hg =>
    obtain ⟨u,hu,he⟩ := hf
    obtain ⟨v,hv,hvE⟩ := hg
    exact ⟨u+v,Submodule.add_mem _ hu hv,by rw [map_add,map_add,he,hvE]⟩
  | smul r f _ hf =>
    obtain ⟨u,hu,he⟩ := hf
    exact ⟨r • u,Submodule.smul_mem _ r hu,by rw [map_smul,map_smul,he]⟩

end RothschildStein.G3

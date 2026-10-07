-- Copyright (c) 2026 Scott Armstrong and Amélie Loher. All rights reserved.
-- Released under Apache 2.0 license as described in the file LICENSE.
module
public import RothschildStein.G3.BasisDilation
public import RothschildStein.G3.CoordinatePolynomials
public import RothschildStein.Definitions.HomogeneousGroup
@[expose] public section
noncomputable section
namespace RothschildStein.G3

/-- Coordinate dilation preserves the BCH coordinate product in a
homogeneous basis (BB Proposition 10.52, p. 529). -/
theorem coordinateDilation_product {a s M : ℕ} {p : Fin a → ℕ+}
    (b : Module.Basis (Fin M) ℝ (formalSpan a s p)) (w : Fin M → ℕ)
    (hw : ∀ j, weightProjection (w j) (b j).val = (b j).val)
    (t : ℝ) (u v : Fin M → ℝ) :
    coordinateDilation w t (coordinateProduct b.equivFun.symm u v) =
      coordinateProduct b.equivFun.symm (coordinateDilation w t u) (coordinateDilation w t v) := by
  apply b.equivFun.symm.injective
  apply Subtype.ext
  rw [basis_coordinateDilation b w hw, coordinateProduct_map,
    coordinateProduct_map, basis_coordinateDilation b w hw, basis_coordinateDilation b w hw]
  exact coefficientDilationHom_bch t
    (formalSpan_positive_order (b.equivFun.symm u).val (b.equivFun.symm u).property)
    (formalSpan_positive_order (b.equivFun.symm v).val (b.equivFun.symm v).property)

/-- The fixed homogeneous-group structure built from the concrete
weighted free Lie algebra and an ordered homogeneous basis
(BB Proposition 10.52 and Theorems 10.31–10.32, pp. 511–512, 528–529). -/
def homogeneousModelOfBasis {a s M : ℕ} {p : Fin a → ℕ+}
    (b : Module.Basis (Fin M) ℝ (formalSpan a s p)) (w : Fin M → ℕ)
    (hM : 0 < M) (hpos : ∀ j, 0 < w j) (hmono : Monotone w)
    (hw : ∀ j, weightProjection (w j) (b j).val = (b j).val) : HomogeneousGroup M where
  dimension_pos := hM
  weight := w
  weight_pos := hpos
  weight_mono := hmono
  productPolynomial := coordinateProductPolynomial b.equivFun.symm
  inversePolynomial := fun j => -MvPolynomial.X j
  zero_left := by
    intro u
    rw [polynomialProduct_coordinateProductPolynomial, coordinateProduct_zero_left]
  zero_right := by
    intro u
    rw [polynomialProduct_coordinateProductPolynomial, coordinateProduct_zero_right]
  assoc := by
    intro u v z
    simp only [polynomialProduct_coordinateProductPolynomial, coordinateProduct_assoc]
  inverse_left := by
    intro u
    simp only [map_neg, MvPolynomial.eval_X]
    rw [polynomialProduct_coordinateProductPolynomial]
    exact coordinateProduct_neg_left _ u
  inverse_right := by
    intro u
    simp only [map_neg, MvPolynomial.eval_X]
    rw [polynomialProduct_coordinateProductPolynomial]
    exact coordinateProduct_neg_right _ u
  dilation_product := by
    intro t _ u v
    simp only [polynomialProduct_coordinateProductPolynomial]
    exact coordinateDilation_product b w hw t u v

/-- A retained generator forces positive fixed free dimension
(BB Proposition 10.48, p. 525). -/
theorem freeDimension_pos_of_generator {a s : ℕ} (p : Fin a → ℕ+)
    (i : Fin a) (hi : (p i : ℕ) ≤ s) : 0 < freeDimension a s p := by
  let f : formalSpan a s p := ⟨truncatedBracket [i],
    truncatedBracket_mem_span [i] (by simp) (by simpa [wordWeight] using hi)⟩
  apply Module.finrank_pos_iff_exists_ne_zero.mpr
  refine ⟨f, ?_⟩
  intro hf
  have he := congrArg (fun g : formalSpan a s p => g.val
    (boundedWord p [i] (by simpa [wordWeight] using hi))) hf
  change truncatedBracket [i] (boundedWord p [i] _) = 0 at he
  simp [truncatedBracket, formalBracket, boundedWordList, boundedWord] at he
end RothschildStein.G3

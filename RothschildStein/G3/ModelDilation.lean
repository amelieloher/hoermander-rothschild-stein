-- Copyright (c) 2026 Scott Armstrong and Amélie Loher. All rights reserved.
-- Released under Apache 2.0 license as described in the file LICENSE.
module
public import RothschildStein.G3.ModelProduct
public import RothschildStein.G3.DilationSpan
@[expose] public section
noncomputable section
namespace RothschildStein.G3

/-- Weighted coefficient dilation as an associative algebra map
(BB Proposition 10.52, p. 529). -/
def coefficientDilationHom {a s : ℕ} {p : Fin a → ℕ+} (t : ℝ) :
    FiniteWordAlgebra a s p →ₐ[ℝ] FiniteWordAlgebra a s p where
  toFun := finiteDilate t
  map_zero' := (dilationLinearMap t).map_zero
  map_add' := (dilationLinearMap t).map_add
  map_mul' := finiteDilate_product t
  map_one' := by
    funext J
    change t ^ wordWeight p J.val * truncatedUnit J = truncatedUnit J
    by_cases h : J.val = []
    · simp [truncatedUnit, restrict, wordUnit, boundedWordList, h, wordWeight]
    · simp [truncatedUnit, restrict, wordUnit, boundedWordList, h]
  commutes' r := by
    funext J
    change t ^ wordWeight p J.val * (r * truncatedUnit J) = r * truncatedUnit J
    by_cases h : J.val = []
    · simp [truncatedUnit, restrict, wordUnit, boundedWordList, h, wordWeight]
    · simp [truncatedUnit, restrict, wordUnit, boundedWordList, h]

/-- Dilation preserves positive coefficient order (BB p. 529). -/
theorem coefficientDilationHom_positive {a s : ℕ} {p : Fin a → ℕ+}
    (t : ℝ) {f : FiniteWordAlgebra a s p} (hf : FiniteOrderAtLeast 1 f) :
    FiniteOrderAtLeast 1 (coefficientDilationHom t f) := by
  rw [finite_positive_order_iff] at hf ⊢
  change t ^ wordWeight p [] * f (boundedWord p [] (by simp [wordWeight])) = 0
  rw [hf, mul_zero]

/-- Dilation preserves the finite BCH law (BB p. 529). -/
theorem coefficientDilationHom_bch {a s : ℕ} {p : Fin a → ℕ+}
    (t : ℝ) {f g : FiniteWordAlgebra a s p}
    (hf : FiniteOrderAtLeast 1 f) (hg : FiniteOrderAtLeast 1 g) :
    coefficientDilationHom t (finiteBCH f g) =
      finiteBCH (coefficientDilationHom t f) (coefficientDilationHom t g) :=
  map_finiteBCH _ (fun _ h => coefficientDilationHom_positive t h) hf hg

/-- Dilation on the concrete model Lie carrier (BB p. 529). -/
def modelDilation {a s : ℕ} {p : Fin a → ℕ+} (t : ℝ)
    (f : coefficientLieAlgebra a s p) : coefficientLieAlgebra a s p :=
  ⟨finiteDilate t f.val, finiteDilate_mem_formalSpan t f.property⟩

/-- Model dilation preserves the model group product (BB p. 529). -/
theorem modelDilation_product {a s : ℕ} {p : Fin a → ℕ+}
    (t : ℝ) (f g : coefficientLieAlgebra a s p) :
    modelDilation t (modelProduct f g) = modelProduct (modelDilation t f) (modelDilation t g) := by
  apply Subtype.ext
  exact coefficientDilationHom_bch t (formalSpan_positive_order f.val f.property)
    (formalSpan_positive_order g.val g.property)
end RothschildStein.G3

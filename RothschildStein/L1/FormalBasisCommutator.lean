-- Copyright (c) 2026 Scott Armstrong and Amélie Loher. All rights reserved.
-- Released under Apache 2.0 license as described in the file LICENSE.
module
public import RothschildStein.L1.CanonicalFormalWordExpansion
public import RothschildStein.G3.FiniteBracketAlphabetEvaluation
public import RothschildStein.L1.HomogeneousWordCoordinates
@[expose] public section
set_option autoImplicit false
set_option relaxedAutoImplicit false
noncomputable section
open Set TopologicalSpace
namespace RothschildStein.L1
open G3

/-- The formal homogeneous basis commutator stays in the formal span `formalSpan`. -/
def formalBasisCommutator {a s : ℕ} {p : Fin a → ℕ+} (D : FreeModelData a s p)
    (i j : Fin (freeDimension a s p)) : formalSpan a s p :=
  ⟨truncatedProduct (D.basis i).val (D.basis j).val -
      truncatedProduct (D.basis j).val (D.basis i).val, by
    have hh := finiteLieSpan_lie_mem (f := ((D.basis i).val : FiniteWordAlgebra a s p))
      (g := ((D.basis j).val : FiniteWordAlgebra a s p))
      (D.basis i).property (D.basis j).property
    exact hh⟩

/-- The formal basis commutator lies in the sum of the two input weights. -/
theorem formalBasisCommutator_homogeneous {a s : ℕ} {p : Fin a → ℕ+}
    (D : FreeModelData a s p) (i j : Fin (freeDimension a s p)) :
    weightProjection (D.weight i + D.weight j) (formalBasisCommutator D i j).val =
      (formalBasisCommutator D i j).val := by
  change weightProjection (D.weight i + D.weight j)
    (truncatedProduct (D.basis i).val (D.basis j).val -
      truncatedProduct (D.basis j).val (D.basis i).val) =
    truncatedProduct (D.basis i).val (D.basis j).val -
      truncatedProduct (D.basis j).val (D.basis i).val
  rw [map_sub]
  have hi := weightProjection_product (D.basis_homogeneous i) (D.basis_homogeneous j)
  have hj := weightProjection_product (D.basis_homogeneous j) (D.basis_homogeneous i)
  rw [Nat.add_comm (D.weight j) (D.weight i)] at hj
  rw [hi,hj]

/-- Only basis coordinates of the summed input weight occur in the bracket. -/
theorem formalBasisCommutator_coordinate_zero {a s : ℕ} {p : Fin a → ℕ+}
    (D : FreeModelData a s p) (i j k : Fin (freeDimension a s p))
    (hk : D.weight k ≠ D.weight i + D.weight j) :
    D.basis.equivFun (formalBasisCommutator D i j) k = 0 :=
  formal_basis_coordinate_zero_of_homogeneous D _ _
    (formalBasisCommutator_homogeneous D i j) k hk

/-- The binary basis-alphabet word evaluates to the exact formal
commutator, before evaluation as actual variable-coefficient operators. -/
theorem basisWordSubstitution_binary {a s : ℕ} {p : Fin a → ℕ+}
    (D : FreeModelData a s p) (i j : Fin (freeDimension a s p)) :
    basisWordSubstitution D (finiteBracketWord [i,j]) = (formalBasisCommutator D i j).val := by
  have hw : (finiteBracketWord [i,j] : FiniteWordAlgebra (freeDimension a s p) s (basisAlphabetWeight D)) =
      ⁅finiteLetter (s := s) (p := basisAlphabetWeight D) i,
        finiteLetter (s := s) (p := basisAlphabetWeight D) j⁆ := by
    exact (nested_eval_truncatedBracket (s := s) (p := basisAlphabetWeight D)
      (Nested.bracket i (Nested.letter j))).symm
  rw [hw,Ring.lie_def,map_sub,map_mul,map_mul]
  simp only [basisWordSubstitution]
  rw [weightedFiniteSubstitutionHom_letter,weightedFiniteSubstitutionHom_letter]
  simp only [finiteBracketWord]
  rw [← (modelBasisWord_spec D i).2.2,← (modelBasisWord_spec D j).2.2]
  rfl

/-- For brackets within the cutoff, the formal commutator represents the
actual bracket of basis-word fields, retaining all coefficient derivatives. -/
theorem actual_basis_bracket_eq_finiteLieField {a s N : ℕ} {p : Fin a → ℕ+}
    (D : FreeModelData a s p) (Ω : Opens (Fin N → ℝ))
    (X : Fin a → (Fin N → ℝ) → (Fin N → ℝ))
    (hX : ∀ i, ContDiffOn ℝ (⊤ : ℕ∞) (X i) Ω)
    (i j : Fin (freeDimension a s p)) (hij : D.weight i + D.weight j ≤ s)
    {x : Fin N → ℝ} (hx : x ∈ Ω) :
    VectorField.lieBracket ℝ (wordBracket X (modelBasisWord D i))
      (wordBracket X (modelBasisWord D j)) x = finiteLieField D X (formalBasisCommutator D i j) x := by
  have he := differentialWordEvaluation_finiteBracketAlphabet (s := s) (basisAlphabetWeight D) Ω X hX
    (modelBasisWord D) (fun k => (modelBasisWord_spec D k).1)
    (fun k => modelBasisWord_weight D k) (finiteBracketWord [i,j])
  change differentialWordEvaluation Ω X hX
      (finitePolynomial (basisWordSubstitution D (finiteBracketWord [i,j]))) = _ at he
  rw [basisWordSubstitution_binary] at he
  have hword : wordWeight (basisAlphabetWeight D) [i,j] ≤ s := by
    simpa only [wordWeight,List.map_cons,List.map_nil,List.sum_cons,List.sum_nil,add_zero,
      basisAlphabetWeight,PNat.mk_coe] using hij
  ext k
  have hh := congrArg (fun T => (T (coordinateTest Ω k)).val x) he
  simp only [finiteBracketWord] at hh
  rw [differentialWordEvaluation_finiteLieField D Ω X hX _ _ hx,
    differentialWordEvaluation_truncatedBracket Ω _ _ [i,j] (by simp) hword,
    smoothFieldOperator_apply Ω _ _ (coordinateTest Ω k) hx] at hh
  change fderiv ℝ ((ContinuousLinearMap.proj k : (Fin N → ℝ) →L[ℝ] ℝ) : (Fin N → ℝ) → ℝ) x
      (finiteLieField D X (formalBasisCommutator D i j) x) =
    fderiv ℝ ((ContinuousLinearMap.proj k : (Fin N → ℝ) →L[ℝ] ℝ) : (Fin N → ℝ) → ℝ) x
      (VectorField.lieBracket ℝ (wordBracket X (modelBasisWord D i)) (wordBracket X (modelBasisWord D j)) x) at hh
  rw [ContinuousLinearMap.fderiv] at hh
  exact hh.symm
end RothschildStein.L1

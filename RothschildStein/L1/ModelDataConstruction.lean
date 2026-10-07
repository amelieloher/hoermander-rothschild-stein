-- Copyright (c) 2026 Scott Armstrong and Amélie Loher. All rights reserved.
-- Released under Apache 2.0 license as described in the file LICENSE.
module

public import RothschildStein.L1.ModelData
public import RothschildStein.L1.BoundedWordStep

set_option autoImplicit false
set_option relaxedAutoImplicit false
set_option backward.isDefEq.respectTransparency false
@[expose] public section
noncomputable section
open Set
open scoped BigOperators
namespace RothschildStein.L1

/-- The common-basis model is constructed from the proved G3
package, without another model-existence premise (BB pp. 511–532). -/
def modelDataOfFreeModel {k s : ℕ} {w : Fin k → ℕ+}
    (D : G3.FreeModelData k s w) : ModelData k s (freeDimension k s w) w := by
  classical
  refine {
    G := D.group
    B := G3.modelBasisWord D
    v := fun i => G3.wordCoordinates D.basis.equivFun.symm [i]
    Y := D.fields
    basis_weight := ?_
    basis_independent := ?_
    basis_span := ?_
    generator_coords := ?_
    inv_eq_neg := G3.freeModel_inv D
    model_field_eq := ?_
    model_field_smooth := G3.freeModel_fields_smooth D
    model_field_invariant := G3.freeModel_fields_leftInvariant D
    model_field_homogeneous := ?_
    model_free := ?_
    model_nilpotent := ?_
    model_basis_origin := by
      intro j
      simpa only [Hormander.Interface.basisVec, G3.FreeModelData.fields] using G3.modelBasisWord_origin D j
    model_exponential := G3.modelBasisWord_radial D }
  · intro j
    exact ⟨(G3.modelBasisWord_spec D j).1, (G3.modelBasisWord_spec D j).2.1,
      (G3.modelBasisWord_weight D j).symm⟩
  · have he : (fun j => (truncatedBracket (G3.modelBasisWord D j) : WordCoefficients k s w)) =
        fun j => (D.basis j).val := funext (fun j => (G3.modelBasisWord_spec D j).2.2.symm)
    rw [he]
    exact D.basis.linearIndependent.map' (formalSpan k s w).subtype (Submodule.ker_subtype _)
  · have he : (fun j => (truncatedBracket (G3.modelBasisWord D j) : WordCoefficients k s w)) =
        (Subtype.val : formalSpan k s w → WordCoefficients k s w) ∘ D.basis :=
      funext (fun j => (G3.modelBasisWord_spec D j).2.2.symm)
    rw [he, Set.range_comp]
    change Submodule.span ℝ ((formalSpan k s w).subtype '' Set.range D.basis) = _
    rw [← Submodule.map_span, D.basis.span_eq, Submodule.map_subtype_top]
  · intro i
    have he := congrArg Subtype.val (D.basis.sum_repr (G3.wordLieElement (s := s) (p := w) [i]))
    have hb : ∀ j, (D.basis j).val = truncatedBracket (G3.modelBasisWord D j) :=
      fun j => (G3.modelBasisWord_spec D j).2.2
    change (∑ j, (D.basis.repr (G3.wordLieElement (s := s) (p := w) [i])) j •
      (truncatedBracket (G3.modelBasisWord D j) : WordCoefficients k s w)) = _
    simpa only [Submodule.coe_sum, Submodule.coe_smul, hb, G3.wordLieElement] using he
  · intro i u
    have he : D.group.mul u = G3.coordinateProduct D.basis.equivFun.symm u :=
      funext (G3.freeModel_mul D u)
    rw [he]
    rfl
  · intro i t ht u
    have he := G3.modelGenerators_homogeneous D i t ht.ne' u
    simpa only [G3.FreeModelData.fields, G3.FreeModelData.group, G3.homogeneousModelOfBasis,
      HomogeneousGroup.dilate, zpow_neg, zpow_natCast] using he
  · intro u
    refine ⟨G3.freeModel_fields_freeAt D u, ?_⟩
    have hs := G3.modelWordSpan_eq_top D.basis.equivFun.symm u
    exact bracketStepOn_of_bounded_word_spans {u} w D.fields
      (fun x hx => by
        rw [Set.mem_singleton_iff.mp hx]
        simpa only [G3.modelWordSpan, G3.FreeModelData.fields] using hs) u (by simp)
  · intro I hI
    rw [G3.FreeModelData.fields, G3.wordBracket_modelGenerators]
    have hz : G3.wordLieElement (s := s) (p := w) I = 0 :=
      Subtype.ext (G3.truncatedBracket_eq_zero_of_weight_gt I hI)
    simp only [G3.wordCoordinates, hz, map_zero]
    funext u
    change fderiv ℝ (G3.coordinateProduct D.basis.equivFun.symm u) 0 0 = 0
    exact map_zero _

end RothschildStein.L1

-- Copyright (c) 2026 Scott Armstrong and Amélie Loher. All rights reserved.
-- Released under Apache 2.0 license as described in the file LICENSE.
module
public import RothschildStein.G3.ModelDilation
public import RothschildStein.G3.SortedModelBasis
public import RothschildStein.Definitions.coordinateDilation
@[expose] public section
noncomputable section
open scoped BigOperators
namespace RothschildStein.G3

/-- A weight-projected vector is an eigenvector of coefficient dilation
(BB (10.53), p. 526). -/
theorem finiteDilate_eq_smul_of_projection {a s k : ℕ} {p : Fin a → ℕ+}
    (f : WordCoefficients a s p) (hf : weightProjection k f = f) (t : ℝ) :
    finiteDilate t f = t ^ k • f := by
  funext J
  by_cases hJ : wordWeight p J.val = k
  · simp [finiteDilate, hJ]
  · have hz : f J = 0 := by
      have h := congrFun hf J
      change (if wordWeight p J.val = k then f J else 0) = f J at h
      simpa only [ite_eq_right hJ] using h.symm
    simp [finiteDilate, hz]

/-- In a homogeneous basis, coefficient dilation is exactly the fixed
coordinate dilation (BB Remark 10.51, p. 528). -/
theorem basis_coordinateDilation {a s M : ℕ} {p : Fin a → ℕ+}
    (b : Module.Basis (Fin M) ℝ (formalSpan a s p)) (w : Fin M → ℕ)
    (hw : ∀ j, weightProjection (w j) (b j).val = (b j).val)
    (t : ℝ) (u : Fin M → ℝ) :
    (b.equivFun.symm (coordinateDilation w t u)).val = finiteDilate t (b.equivFun.symm u).val := by
  change (formalSpan a s p).subtype (b.equivFun.symm (coordinateDilation w t u)) =
    dilationLinearMap t ((formalSpan a s p).subtype (b.equivFun.symm u))
  rw [b.equivFun_symm_apply, b.equivFun_symm_apply, map_sum, map_sum, map_sum]
  simp only [map_smul]
  apply Finset.sum_congr rfl
  intro j _
  change (t ^ w j * u j) • (b j).val = u j • finiteDilate t (b j).val
  rw [finiteDilate_eq_smul_of_projection _ (hw j) t, smul_smul, mul_comm]
end RothschildStein.G3

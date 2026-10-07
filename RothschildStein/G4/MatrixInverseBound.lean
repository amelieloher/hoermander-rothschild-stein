-- Copyright (c) 2026 Scott Armstrong and Amélie Loher. All rights reserved.
-- Released under Apache 2.0 license as described in the file LICENSE.
module

public import RothschildStein.G4.MatrixOperatorBound
public import RothschildStein.G1.ChartInverseRegularity

@[expose] public section
set_option autoImplicit false
set_option relaxedAutoImplicit false
noncomputable section

namespace RothschildStein.G4

/-- A normalized error of operator norm at most 1/4 has an inverse
of norm at most 4/3, including dimension zero. The existence proof uses
finite-dimensional injectivity; the norm bound is the geometric-series bound
proved directly from the forward identity (BB Lemma 9.51, pp. 446–447). -/
theorem identity_add_matrixOperator_inverse {n : ℕ}
    (M : Matrix (Fin n) (Fin n) ℝ) {κ : ℝ} (hκ : 0 ≤ κ)
    (hM : ∀ i j, |M i j| ≤ κ) (hsmall : (n : ℝ) * κ ≤ 1 / 4) :
    ∃ L : (Fin n → ℝ) ≃L[ℝ] (Fin n → ℝ),
      (L : (Fin n → ℝ) →L[ℝ] (Fin n → ℝ)) = ContinuousLinearMap.id ℝ (Fin n → ℝ) + matrixOperator M ∧
      ‖(L.symm : (Fin n → ℝ) →L[ℝ] (Fin n → ℝ))‖ ≤ 4 / 3 := by
  have hnorm := (matrixOperator_norm_le M hκ hM).trans hsmall
  obtain ⟨L, hL, _⟩ := RothschildStein.G1.chart_linearPerturbation_inverse
    (ContinuousLinearEquiv.refl ℝ (Fin n → ℝ))
    (ContinuousLinearMap.id ℝ (Fin n → ℝ) + matrixOperator M) (P := 1) (by norm_num)
    (ContinuousLinearMap.norm_id_le (𝕜 := ℝ) (E := Fin n → ℝ)) (by
      simpa only [ContinuousLinearEquiv.coe_refl, add_sub_cancel_left, mul_one, one_div] using
        hnorm.trans (show (1 : ℝ) / 4 ≤ 1 / 2 by norm_num))
  refine ⟨L, hL, ?_⟩
  apply ContinuousLinearMap.opNorm_le_bound _ (by norm_num)
  intro v
  let u := L.symm v
  have hu : (ContinuousLinearMap.id ℝ (Fin n → ℝ) + matrixOperator M) u = v := by
    rw [← hL]; exact L.apply_symm_apply v
  have heq : u = v - matrixOperator M u := by
    have hsum : u + matrixOperator M u = v := by simpa only [add_apply, ContinuousLinearMap.id_apply] using hu
    exact eq_sub_of_add_eq hsum
  have h := calc
    ‖u‖ = ‖v - matrixOperator M u‖ := congrArg norm heq
    _ ≤ ‖v‖ + ‖matrixOperator M u‖ := norm_sub_le _ _
    _ ≤ ‖v‖ + ‖matrixOperator M‖ * ‖u‖ := add_le_add le_rfl ((matrixOperator M).le_opNorm u)
    _ ≤ ‖v‖ + (1 / 4 : ℝ) * ‖u‖ := add_le_add le_rfl
      (mul_le_mul_of_nonneg_right hnorm (norm_nonneg u))
  change ‖u‖ ≤ (4 / 3 : ℝ) * ‖v‖
  linarith

end RothschildStein.G4

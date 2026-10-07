-- Copyright (c) 2026 Scott Armstrong and Amélie Loher. All rights reserved.
-- Released under Apache 2.0 license as described in the file LICENSE.
module

public import Mathlib.Analysis.Calculus.ContDiff.Bounds
public import Mathlib.Analysis.Calculus.ContDiff.Comp
public import Mathlib.Analysis.Normed.Operator.Bilinear

set_option autoImplicit false
set_option relaxedAutoImplicit false
@[expose] public section
noncomputable section
namespace RothschildStein.P1

/-- Restricting the differential to base directions costs no
factor in any derivative seminorm. -/
theorem norm_iteratedFDeriv_baseDifferential_le {n d : ℕ} {B : Type*}
    [NormedAddCommGroup B] [NormedSpace ℝ B]
    {F : ((Fin n → ℝ) × (Fin d → ℝ)) → B}
    (hF : ContDiff ℝ (⊤ : ℕ∞) F) (m : ℕ)
    (p : (Fin n → ℝ) × (Fin d → ℝ)) :
    ‖iteratedFDeriv ℝ m (fun y => (fderiv ℝ F y).comp
      (ContinuousLinearMap.inl ℝ (Fin n → ℝ) (Fin d → ℝ))) p‖ ≤
      ‖iteratedFDeriv ℝ (m + 1) F p‖ := by
  let L := (ContinuousLinearMap.compL ℝ (Fin n → ℝ)
    ((Fin n → ℝ) × (Fin d → ℝ)) B).flip
      (ContinuousLinearMap.inl ℝ (Fin n → ℝ) (Fin d → ℝ))
  have hL : ‖L‖ ≤ 1 := by
    apply L.opNorm_le_bound (by norm_num)
    intro A
    change ‖A.comp (ContinuousLinearMap.inl ℝ (Fin n → ℝ) (Fin d → ℝ))‖ ≤ 1 * ‖A‖
    calc
      _ ≤ ‖A‖ * ‖ContinuousLinearMap.inl ℝ (Fin n → ℝ) (Fin d → ℝ)‖ := A.opNorm_comp_le _
      _ ≤ ‖A‖ * 1 := mul_le_mul_of_nonneg_left
        (ContinuousLinearMap.norm_inl_le_one ℝ (Fin n → ℝ) (Fin d → ℝ)) (norm_nonneg A)
      _ = _ := by ring
  have h := L.norm_iteratedFDeriv_comp_left (x := p)
    (contDiff_infty_iff_fderiv.mp hF).2.contDiffAt (n := m) (by simp)
  change ‖iteratedFDeriv ℝ m (L ∘ fderiv ℝ F) p‖ ≤ _
  exact h.trans ((mul_le_mul_of_nonneg_right hL (norm_nonneg _)).trans_eq
    (by rw [one_mul, norm_iteratedFDeriv_fderiv]))

end RothschildStein.P1

-- Copyright (c) 2026 Scott Armstrong and Amélie Loher. All rights reserved.
-- Released under Apache 2.0 license as described in the file LICENSE.
module

public import RothschildStein.S.HadamardCoefficients
public import Mathlib.Analysis.Calculus.FDeriv.Mul

set_option autoImplicit false
set_option relaxedAutoImplicit false
@[expose] public section
noncomputable section
open Set MeasureTheory Function
open scoped Topology ContDiff
namespace RothschildStein.S
variable {n : ℕ}

/-- Differentiating the coefficient quotient in the y-direction
cancels the ε factor exactly (BB p. 76; chain-rule). -/
theorem coefficientDifferenceQuotient_fderiv_y {b : (Fin n → ℝ) → ℝ}
    (hb : ContDiff ℝ (⊤ : ℕ∞) b) {ε : ℝ} (hε : ε ≠ 0)
    (x y v : Fin n → ℝ) :
    fderiv ℝ (coefficientDifferenceQuotient b ε x) y v =
      fderiv ℝ b (x+ε • y) v := by
  have ha : HasFDerivAt (fun y : Fin n → ℝ => x+ε • y)
      (ε • ContinuousLinearMap.id ℝ (Fin n → ℝ)) y :=
    ((hasFDerivAt_id y).const_smul ε).const_add x
  have hb' := (hb.differentiable (by simp)).differentiableAt.hasFDerivAt.comp y ha
  simp only [Function.comp_def] at hb'
  have hd := (hb'.sub_const (b x)).const_mul ε⁻¹
  change fderiv ℝ (fun y => ε⁻¹ * (b (x+ε • y)-b x)) y v = _
  rw [hd.fderiv]
  change ε⁻¹ * (fderiv ℝ b (x+ε • y) (ε • v)) = _
  rw [ContinuousLinearMap.map_smul,smul_eq_mul,← mul_assoc,inv_mul_cancel₀ hε,one_mul]

end RothschildStein.S

-- Copyright (c) 2026 Scott Armstrong and Amélie Loher. All rights reserved.
-- Released under Apache 2.0 license as described in the file LICENSE.
module

public import RothschildStein.H2.OperatorAllExponents

@[expose] public section
set_option autoImplicit false
set_option relaxedAutoImplicit false
noncomputable section

namespace RothschildStein.H2

/-- Nonnegativity of the explicit interpolation coefficient
(BB p. 326). -/
theorem operatorInterpolationConstant_nonneg {C cT p : ℝ} (hC : 0 ≤ C)
    (hp : 1 < p) (hp2 : p < 2) : 0 ≤ operatorInterpolationConstant C cT p := by
  have hp0 : 0 < p := by linarith
  have hpm : 0 < p - 1 := by linarith
  have hmp : 0 < 2 - p := by linarith
  apply Real.rpow_nonneg
  positivity

/-- Nonnegativity of the all-exponent coefficient
(BB p. 326). -/
theorem operatorAllExponentConstant_nonneg {C Cs cT p : ℝ}
    (hC : 0 ≤ C) (hCs : 0 ≤ Cs) (hcT : 0 ≤ cT) (hp : 1 < p) :
    0 ≤ operatorAllExponentConstant C Cs cT p := by
  unfold operatorAllExponentConstant
  split_ifs with hlt heq
  · exact operatorInterpolationConstant_nonneg hC hp hlt
  · exact hcT
  · have hpq := Real.HolderConjugate.conjExponent hp
    have hq2 : Real.conjExponent p < 2 := by
      change p / (p - 1) < 2
      apply (div_lt_iff₀ (by linarith : 0 < p - 1)).mpr
      have hgt : 2 < p := lt_of_le_of_ne (le_of_not_gt hlt) (Ne.symm heq)
      linarith
    exact operatorInterpolationConstant_nonneg hCs hpq.symm.lt hq2

end RothschildStein.H2

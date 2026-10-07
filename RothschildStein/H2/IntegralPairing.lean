-- Copyright (c) 2026 Scott Armstrong and Amélie Loher. All rights reserved.
-- Released under Apache 2.0 license as described in the file LICENSE.
module

public import Mathlib.MeasureTheory.Integral.Bochner.Basic
public import Mathlib.MeasureTheory.Function.LpSeminorm.CompareExp

@[expose] public section
set_option autoImplicit false
set_option relaxedAutoImplicit false
noncomputable section
open Set MeasureTheory
open scoped ENNReal

namespace RothschildStein.H2
variable {X : Type*} [MeasurableSpace X]

/-- Hölder's bound for the actual integral pairing, expressed
in the same extended norms as the interpolation estimates
(BB p. 326). -/
theorem integral_pairing_le_eLpNorm (μ : Measure X) {f g : X → ℝ} {p q : ℝ}
    (hpq : p.HolderConjugate q) (hf : MemLp f (ENNReal.ofReal p) μ)
    (hg : MemLp g (ENNReal.ofReal q) μ) :
    |∫ x, f x * g x ∂μ| ≤ (eLpNorm f (ENNReal.ofReal p) μ).toReal *
      (eLpNorm g (ENNReal.ofReal q) μ).toReal := by
  have hp0 : 0 < p := hpq.pos
  have hq0 : 0 < q := hpq.symm.pos
  have hfroot : 0 ≤ (∫ x, ‖f x‖ ^ p ∂μ) ^ (1 / p) :=
    Real.rpow_nonneg (integral_nonneg fun x => Real.rpow_nonneg (norm_nonneg _) _) _
  have hgroot : 0 ≤ (∫ x, ‖g x‖ ^ q ∂μ) ^ (1 / q) :=
    Real.rpow_nonneg (integral_nonneg fun x => Real.rpow_nonneg (norm_nonneg _) _) _
  calc
    _ ≤ ∫ x, ‖f x * g x‖ ∂μ := by
      simpa only [Real.norm_eq_abs] using norm_integral_le_integral_norm (fun x => f x * g x)
    _ = ∫ x, ‖f x‖ * ‖g x‖ ∂μ := by simp only [norm_mul]
    _ ≤ (∫ x, ‖f x‖ ^ p ∂μ) ^ (1 / p) * (∫ x, ‖g x‖ ^ q ∂μ) ^ (1 / q) :=
      integral_mul_norm_le_Lp_mul_Lq hpq hf hg
    _ = _ := by
      rw [hf.eLpNorm_eq_integral_rpow_norm (by positivity : ENNReal.ofReal p ≠ 0) ENNReal.ofReal_ne_top,
        hg.eLpNorm_eq_integral_rpow_norm (by positivity : ENNReal.ofReal q ≠ 0) ENNReal.ofReal_ne_top]
      simp only [ENNReal.toReal_ofReal hpq.nonneg, ENNReal.toReal_ofReal hpq.symm.nonneg, ← one_div]
      rw [ENNReal.toReal_ofReal hfroot, ENNReal.toReal_ofReal hgroot]

end RothschildStein.H2

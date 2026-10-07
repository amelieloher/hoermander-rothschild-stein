-- Copyright (c) 2026 Scott Armstrong and Amélie Loher. All rights reserved.
-- Released under Apache 2.0 license as described in the file LICENSE.
module

public import RothschildStein.H3.CutoffStepToReal

set_option autoImplicit false
set_option relaxedAutoImplicit false
@[expose] public section
noncomputable section
open scoped ENNReal
namespace RothschildStein.H3

/-- The finite actual cutoff coefficient estimate converts
exactly to real norms before the quarter-contraction scale is chosen. -/
theorem holder_cutoff_coefficients_toReal {x F U P : ℝ≥0∞} {ε A B C γ : ℝ}
    (hF : F ≠ ⊤) (hU : U ≠ ⊤) (hP : P ≠ ⊤)
    (hε : 0 < ε) (hA : 0 ≤ A) (hB : 0 ≤ B) (hC : 0 ≤ C)
    (h : x ≤ ENNReal.ofReal ε * (F + ENNReal.ofReal B * U +
      2 * ENNReal.ofReal A * P) + ENNReal.ofReal (C * ε ^ (-γ)) * U) :
    x.toReal ≤ ε * (F.toReal + B * U.toReal + 2 * A * P.toReal) +
      C * ε ^ (-γ) * U.toReal := by
  have hfin : ENNReal.ofReal ε * (F + ENNReal.ofReal B * U +
      2 * ENNReal.ofReal A * P) + ENNReal.ofReal (C * ε ^ (-γ)) * U ≠ ⊤ := by
    finiteness
  have hr := ENNReal.toReal_mono hfin h
  rw [ENNReal.toReal_add (by finiteness) (by finiteness)] at hr
  simp only [ENNReal.toReal_mul] at hr
  rw [ENNReal.toReal_add (by finiteness) (by finiteness),
    ENNReal.toReal_add hF (by finiteness)] at hr
  simpa only [ENNReal.toReal_mul, ENNReal.toReal_ofNat,
    ENNReal.toReal_ofReal hε.le, ENNReal.toReal_ofReal hA,
    ENNReal.toReal_ofReal hB,
    ENNReal.toReal_ofReal (mul_nonneg hC (Real.rpow_nonneg hε.le _))] using hr

end RothschildStein.H3

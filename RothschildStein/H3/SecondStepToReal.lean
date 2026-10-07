-- Copyright (c) 2026 Scott Armstrong and Amélie Loher. All rights reserved.
-- Released under Apache 2.0 license as described in the file LICENSE.
module

public import RothschildStein.H3.CutoffStepToReal

set_option autoImplicit false
set_option relaxedAutoImplicit false
@[expose] public section
noncomputable section
namespace RothschildStein.H3
open scoped ENNReal

/-- Finite extended norms in the second-order cutoff step give the real
estimate used in Phi absorption, with every coefficient unchanged. -/
theorem second_norm_step_toReal {x F U V : ℝ≥0∞} (n q : ℕ) {C A B : ℝ}
    (hF : F ≠ ⊤) (hU : U ≠ ⊤) (hV : V ≠ ⊤)
    (hC : 0 ≤ C) (hA : 0 ≤ A) (hB : 0 ≤ B)
    (hb : x ≤ (n : ℝ≥0∞) * ENNReal.ofReal C *
      (F + (q+1 : ℝ≥0∞) * ENNReal.ofReal B * U +
        2 * ENNReal.ofReal A * V)) :
    x.toReal ≤ (n : ℝ) * C *
      (F.toReal + (q+1 : ℝ) * B * U.toReal + 2 * A * V.toReal) := by
  have hfin : (n : ℝ≥0∞) * ENNReal.ofReal C *
      (F + (q+1 : ℝ≥0∞) * ENNReal.ofReal B * U +
        2 * ENNReal.ofReal A * V) ≠ ⊤ := by finiteness
  have hr := ENNReal.toReal_mono hfin hb
  rw [ENNReal.toReal_mul, ENNReal.toReal_mul,
    ENNReal.toReal_add (by finiteness) (by finiteness),
    ENNReal.toReal_add hF (by finiteness)] at hr
  have hq : ((q : ℝ≥0∞) + 1).toReal = (q : ℝ) + 1 := by
    rw [ENNReal.toReal_add (by finiteness) (by finiteness)]
    simp only [ENNReal.toReal_natCast, ENNReal.toReal_one]
  simpa only [hq, ENNReal.toReal_mul, ENNReal.toReal_natCast,
    ENNReal.toReal_ofReal hC, ENNReal.toReal_ofReal hA, ENNReal.toReal_ofReal hB,
    ENNReal.toReal_ofNat, ENNReal.toReal_add (by finiteness) (by finiteness)] using hr

end RothschildStein.H3

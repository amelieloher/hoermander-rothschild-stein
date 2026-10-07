-- Copyright (c) 2026 Scott Armstrong and Amélie Loher. All rights reserved.
-- Released under Apache 2.0 license as described in the file LICENSE.
module

public import RothschildStein.H3.CutoffInterpolation
public import Mathlib.Basic.ENNReal.Real

set_option autoImplicit false
set_option relaxedAutoImplicit false
@[expose] public section
noncomputable section
namespace RothschildStein.H3
open scoped ENNReal

/-- The finite weak-norm cutoff estimate becomes the real one-step estimate
used for Phi absorption, with no change to its cutoff coefficients. -/
theorem cutoff_step_toReal {x U V W : ℝ≥0∞} {ε A B q : ℝ}
    (hU : U ≠ ⊤) (hV : V ≠ ⊤) (hW : W ≠ ⊤)
    (hε : 0 < ε) (hA : 0 ≤ A) (hB : 0 ≤ B) (hq : 0 ≤ q)
    (h : x ≤ ENNReal.ofReal (2*q/ε)*U + ENNReal.ofReal (ε/2)*
      (W + 2*ENNReal.ofReal A*V + ENNReal.ofReal q*ENNReal.ofReal B*U)) :
    x.toReal ≤ ε*(W.toReal + 2*A*V.toReal + q*B*U.toReal) +
      (2*q/ε)*U.toReal := by
  have hfin : ENNReal.ofReal (2*q/ε)*U + ENNReal.ofReal (ε/2)*
      (W + 2*ENNReal.ofReal A*V + ENNReal.ofReal q*ENNReal.ofReal B*U) ≠ ⊤ := by
    finiteness
  have hr := ENNReal.toReal_mono hfin h
  have he : (ENNReal.ofReal (2*q/ε)*U + ENNReal.ofReal (ε/2)*
      (W + 2*ENNReal.ofReal A*V + ENNReal.ofReal q*ENNReal.ofReal B*U)).toReal =
      (2*q/ε)*U.toReal + (ε/2)*(W.toReal + 2*A*V.toReal + q*B*U.toReal) := by
    rw [ENNReal.toReal_add (by finiteness) (by finiteness)]
    simp only [ENNReal.toReal_mul]
    rw [ENNReal.toReal_add (by finiteness) (by finiteness),
      ENNReal.toReal_add hW (by finiteness)]
    simp only [ENNReal.toReal_mul, ENNReal.toReal_ofNat]
    rw [ENNReal.toReal_ofReal (by positivity : 0 ≤ 2*q/ε),
      ENNReal.toReal_ofReal (by positivity : 0 ≤ ε/2), ENNReal.toReal_ofReal hA,
      ENNReal.toReal_ofReal hq, ENNReal.toReal_ofReal hB]
  rw [he] at hr
  have hn : 0 ≤ W.toReal + 2*A*V.toReal + q*B*U.toReal := by positivity
  nlinarith

end RothschildStein.H3

-- Copyright (c) 2026 Scott Armstrong and Amélie Loher. All rights reserved.
-- Released under Apache 2.0 license as described in the file LICENSE.
module

public import Hormander.E.OneStep.ExtAlgebra
public import Hormander.A.SobolevScale

@[expose] public section

noncomputable section

open MeasureTheory SchwartzMap

namespace Hormander.E
open Hormander.B

variable {N : ℕ}

/-- for a bundled extendable operator, with the right cutoff. -/
theorem ExtOp.transfer (S : ExtOp N) {m r : ℝ} {C : NNReal}
    (hC : ∀ φ : TestFunction N, sobolevNorm r (S.op φ) ≤ (C : ℝ) * sobolevNorm (r + m) φ)
    (ζ : SchwartzMap (Carrier N) ℝ) (hfac : S.op = S.op.comp (realMultiplierOperator ζ))
    (u : Tempered N) (w : Hormander.A.SobolevSpace N (r + m)) (hw : w.toDistr = cutoffDistr ζ u) :
    S.ext u = S.ext w.toDistr ∧
      ∃ v : Hormander.A.SobolevSpace N r, v.toDistr = S.ext u ∧ ‖v‖ ≤ (C : ℝ) * ‖w‖ :=
  localized_sobolev_bound S.isTr S.cont hC ζ hfac u w hw

/-- Global version: no cutoff. -/
theorem ExtOp.transfer_global (S : ExtOp N) {m r : ℝ} {C : NNReal}
    (hC : ∀ φ : TestFunction N, sobolevNorm r (S.op φ) ≤ (C : ℝ) * sobolevNorm (r + m) φ)
    (w : Hormander.A.SobolevSpace N (r + m)) :
    ∃ v : Hormander.A.SobolevSpace N r, v.toDistr = S.ext w.toDistr ∧ ‖v‖ ≤ (C : ℝ) * ‖w‖ :=
  tempExtension_sobolev S.isTr S.cont hC w

end Hormander.E

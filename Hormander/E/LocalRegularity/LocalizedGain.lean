-- Copyright (c) 2026 Scott Armstrong and Amélie Loher. All rights reserved.
-- Released under Apache 2.0 license as described in the file LICENSE.
module

public import Hormander.D.Assembly.LocalizedGain
public import Hormander.E.LocalRegularity.OneStep

/-!
# Localized gain for one-step regularization

The statement `D1Hypothesis` is supplied by the D assembly
`Hormander.D.localized_gain_of_offDiagonal`, which assumes the off-diagonal smoothing bound
`Hormander.D.OffDiagonalSmoothing`.
-/

@[expose] public section

noncomputable section

open SchwartzMap TemperedDistribution

namespace Hormander.E

/-- The localized gain statement used by the one-step regularization estimate, under the
off-diagonal smoothing hypothesis. -/
theorem d1Hypothesis_of_offDiagonal (hB8 : ∀ N, Hormander.D.OffDiagonalSmoothing N) :
    D1Hypothesis := by
  intro k N X c hX hXc hc hcc K U hK hU hKU s hs w hws hw η₁ η₂ hη hη₂K σ
  exact Hormander.D.localized_gain_of_offDiagonal X c hX hXc hc hcc hK hU hKU s hs w hws hw
    η₁ η₂ hη hη₂K σ (hB8 N)

end Hormander.E

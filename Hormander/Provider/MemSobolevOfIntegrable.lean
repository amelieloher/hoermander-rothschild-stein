-- Copyright (c) 2026 Scott Armstrong and Amélie Loher. All rights reserved.
-- Released under Apache 2.0 license as described in the file LICENSE.
module

public import Hormander.A.Integrable

/-!
# Sobolev regularity of integrable functions

This module provides the negative-order Sobolev estimate for integrable functions.
-/

@[expose] public section

open MeasureTheory

namespace Hormander.Provider

/-- An integrable function belongs to every negative-order Sobolev space. -/
theorem memSobolev_neg_of_integrable {N : ℕ}
    {v : EuclideanSpace ℝ (Fin N) → ℂ} (hv : Integrable v) {m : ℝ}
    (hm : (N : ℝ) < 2 * m) :
    TemperedDistribution.MemSobolev (-m) 2
      (Lp.toTemperedDistribution (hv.toL1 v)) :=
  Hormander.A.memSobolev_neg_of_integrable hv hm

end Hormander.Provider

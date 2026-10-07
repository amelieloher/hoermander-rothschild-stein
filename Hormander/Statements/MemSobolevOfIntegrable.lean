-- Copyright (c) 2026 Scott Armstrong and Amélie Loher. All rights reserved.
-- Released under Apache 2.0 license as described in the file LICENSE.
module

public import Mathlib.Analysis.Distribution.Sobolev
public import Mathlib.Analysis.InnerProductSpace.PiL2
public import Hormander.Provider.MemSobolevOfIntegrable

@[expose] public section

noncomputable section

open MeasureTheory SchwartzMap

namespace Hormander

/-- BB Prop. 5.17: an integrable function on `ℝᴺ` defines a tempered
distribution of Sobolev order `-m` for every `m > N/2`. -/
theorem memSobolev_neg_of_integrable {N : ℕ} {v : EuclideanSpace ℝ (Fin N) → ℂ}
    (hv : Integrable v) {m : ℝ} (hm : (N : ℝ) < 2 * m) :
    TemperedDistribution.MemSobolev (-m) 2
      (Lp.toTemperedDistribution (hv.toL1 v)) :=
  by exact Hormander.Provider.memSobolev_neg_of_integrable hv hm

end Hormander

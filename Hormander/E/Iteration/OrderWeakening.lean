-- Copyright (c) 2026 Scott Armstrong and Amélie Loher. All rights reserved.
-- Released under Apache 2.0 license as described in the file LICENSE.
module

public import Hormander.B.Defs
public import Mathlib.Analysis.Distribution.Sobolev

@[expose] public section

noncomputable section

open SchwartzMap TemperedDistribution
open Hormander.B

namespace Hormander.E

/-- A negative-order Sobolev input of arbitrary real order `-m` may be
weakened to a strictly negative order `-M` with `M > 0` and `m ≤ M` (take `M = max m 1`), so the
positivity hypothesis of the estimate is met. -/
theorem order_weakening {N : ℕ} {m : ℝ} {T : 𝓢'(Carrier N, ℂ)}
    (hT : TemperedDistribution.MemSobolev (-m) 2 T) :
    ∃ M : ℝ, 0 < M ∧ m ≤ M ∧ TemperedDistribution.MemSobolev (-M) 2 T := by
  refine ⟨max m 1, lt_of_lt_of_le one_pos (le_max_right m 1), le_max_left m 1, ?_⟩
  exact hT.mono (by linarith [le_max_left m 1])

end Hormander.E

end

-- Copyright (c) 2026 Scott Armstrong and Amélie Loher. All rights reserved.
-- Released under Apache 2.0 license as described in the file LICENSE.
module

public import RothschildStein.L1.FiberImageVolume
public import RothschildStein.L1.FiberChartVolume

@[expose] public section
set_option autoImplicit false
set_option relaxedAutoImplicit false
noncomputable section
open Set MeasureTheory
open scoped ENNReal

namespace RothschildStein.L1

/-- Inclusion of ambient sets gives inclusion of their
fibers, without any measurability assumption. -/
theorem fiberVolume_mono {n m : ℕ} {A B : Set (Fin (n + m) → ℝ)}
    (hAB : A ⊆ B) (y : Fin n → ℝ) :
    fiberVolume (m := m) A y ≤ fiberVolume B y :=
  measure_mono (fun _ hz => hAB hz)

end RothschildStein.L1

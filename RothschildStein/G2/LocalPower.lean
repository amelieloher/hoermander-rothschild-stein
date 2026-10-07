-- Copyright (c) 2026 Scott Armstrong and Amélie Loher. All rights reserved.
-- Released under Apache 2.0 license as described in the file LICENSE.
module

public import RothschildStein.G2.PowerBochner
public import Mathlib.MeasureTheory.Function.LocallyIntegrable

set_option autoImplicit false
set_option relaxedAutoImplicit false
@[expose] public section
noncomputable section
open Set MeasureTheory
namespace RothschildStein.G2

/-- A gauge power is locally integrable on the full carrier exactly
when β < Q (BB Prop 3.21, pp. 105–106). Compact sets lie in a gauge sublevel. -/
theorem locallyIntegrable_power_iff {N : ℕ} {G : HomogeneousGroup N}
    {ν : (Fin N → ℝ) → ℝ} (hν : G.IsHomogeneousGauge ν) (β : ℝ) :
    LocallyIntegrable (fun x => (ν x) ^ (-β)) ↔ β < G.homogeneousDimension := by
  constructor
  · intro h
    exact (integrableOn_power_near_iff hν β zero_lt_one).mp
      (h.integrableOn_isCompact (isCompact_gauge_le hν 1))
  · intro hβ
    rw [locallyIntegrable_iff]
    intro K hK
    obtain ⟨M, hM⟩ := hK.bddAbove_image hν.1.continuousOn
    apply ((integrableOn_power_near_iff hν β (zero_lt_one.trans_le (le_max_left 1 M))).mpr hβ).mono_set
    intro x hx
    exact (hM ⟨x, hx, rfl⟩).trans (le_max_right 1 M)

end RothschildStein.G2

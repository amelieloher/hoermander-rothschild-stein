-- Copyright (c) 2026 Scott Armstrong and Amélie Loher. All rights reserved.
-- Released under Apache 2.0 license as described in the file LICENSE.
module
public import RothschildStein.H2.UniformVolume
@[expose] public section
set_option autoImplicit false
set_option relaxedAutoImplicit false
noncomputable section
open Set MeasureTheory Metric
open scoped ENNReal
namespace RothschildStein.H2
variable {X : Type*} [MetricSpace X] [MeasurableSpace X] [BorelSpace X]

/-- A finite positive real lower volume supplies the local Lᵖ constants,
including when the centre set is empty. -/
theorem LocDoubling.exists_uniform_real_volume (D : LocDoubling X) :
    ∃ m : ℝ, 0 < m ∧ ∀ z ∈ D.Ω₁, ENNReal.ofReal m ≤ D.μ (ball z D.κ) := by
  obtain ⟨c, hc, hb⟩ := D.outerPatch.exists_uniform_lower D.κ_pos (by change D.κ ≤ 6 * D.κ; linarith [D.κ_pos])
  let m := min c 1
  have hm : 0 < m := lt_min hc (by norm_num)
  have hmt : m < ⊤ := (min_le_right c 1).trans_lt (by norm_num)
  refine ⟨m.toReal, ENNReal.toReal_pos hm.ne' hmt.ne, ?_⟩
  intro z hz
  rw [ENNReal.ofReal_toReal hmt.ne]
  exact (min_le_left c 1).trans (hb z hz)
end RothschildStein.H2

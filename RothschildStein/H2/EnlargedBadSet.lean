-- Copyright (c) 2026 Scott Armstrong and Amélie Loher. All rights reserved.
-- Released under Apache 2.0 license as described in the file LICENSE.
module

public import RothschildStein.H2.VolumeComparison

@[expose] public section
set_option autoImplicit false
set_option relaxedAutoImplicit false
noncomputable section
open Set MeasureTheory Metric
open scoped ENNReal BigOperators

namespace RothschildStein.H2
variable {X ι : Type*} [MetricSpace X] [MeasurableSpace X] [BorelSpace X] [Countable ι]

/-- The union of fourfold bad balls costs two doublings
(BB pp. 319–320). -/
theorem DoublingPatch.enlarged_bad_set_measure (P : DoublingPatch X)
    (z : ι → X) (r : ι → ℝ) (hz : ∀ i, z i ∈ P.S)
    (hr : ∀ i, 0 < r i) (hcap : ∀ i, 5 * r i ≤ P.ρ) :
    P.μ (⋃ i, ball (z i) (4 * r i)) ≤
      ENNReal.ofReal P.C_D ^ 2 * ∑' i, P.μ (ball (z i) (r i)) := by
  calc
    _ ≤ ∑' i, P.μ (ball (z i) (4 * r i)) := measure_iUnion_le _
    _ ≤ ∑' i, ENNReal.ofReal P.C_D ^ 2 * P.μ (ball (z i) (r i)) := by
      apply ENNReal.tsum_le_tsum
      intro i
      exact P.compare_pow (hz i) (hr i) (mul_pos (by norm_num) (hr i))
        (by linarith [hcap i, P.ρ_pos]) 2 (by norm_num)
    _ = _ := ENNReal.tsum_mul_left

end RothschildStein.H2

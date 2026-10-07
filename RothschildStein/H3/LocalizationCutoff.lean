-- Copyright (c) 2026 Scott Armstrong and Amélie Loher. All rights reserved.
-- Released under Apache 2.0 license as described in the file LICENSE.
module

public import RothschildStein.H2.Cutoffs
public import RothschildStein.H2.LocalizedKernelDefs

set_option autoImplicit false
set_option relaxedAutoImplicit false
@[expose] public section
noncomputable section
namespace RothschildStein.H3
open Set Metric
variable {X : Type*} [MetricSpace X]

/-- The common localization cutoff, with inner radius one and outer
radius three halves (BB pp. 357–359, corrected setting R = 2). -/
def localizationCutoff (o : X) : X → ℝ := H2.ballCutoff o 1 (3 / 2)

/-- The cutoff has Lipschitz constant two, is unit-interval valued,
and vanishes outside the localization ball of radius two. -/
theorem localizationCutoff_kernelCutoff (o : X) :
    H2.KernelCutoff (ball o 2) 2 (localizationCutoff o) := by
  refine ⟨?_, fun x => (H2.ballCutoff_bounds o 1 (3 / 2) x).1,
    fun x => (H2.ballCutoff_bounds o 1 (3 / 2) x).2, ?_⟩
  · have h := H2.ballCutoff_lipschitz (x₀ := o) (r := 1) (R := 3 / 2) (by norm_num)
    norm_num at h
    exact h
  · intro x hx
    apply H2.ballCutoff_eq_zero (by norm_num)
    have hd : 2 ≤ dist x o := le_of_not_gt hx
    linarith

/-- The cutoff is exactly one on the closed unit ball. -/
theorem localizationCutoff_eq_one (o : X) {x : X} (hx : x ∈ closedBall o 1) :
    localizationCutoff o x = 1 :=
  H2.ballCutoff_eq_one (by norm_num) hx

end RothschildStein.H3

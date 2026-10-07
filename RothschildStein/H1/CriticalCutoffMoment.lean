-- Copyright (c) 2026 Scott Armstrong and Amélie Loher. All rights reserved.
-- Released under Apache 2.0 license as described in the file LICENSE.
module

public import RothschildStein.H1.HomogeneousBallWeightedScaling

set_option autoImplicit false
set_option relaxedAutoImplicit false
@[expose] public section
noncomputable section
open Set MeasureTheory
namespace RothschildStein.H1
variable {N : ℕ} (G : HomogeneousGroup N)

/-- Step 4: at critical kernel degree, the regularized
small-ball cutoff moment is independent of the dilation parameter. -/
theorem integral_criticalCutoffMoment_scale
    {ν F η : (Fin N → ℝ) → ℝ} (hν : G.IsHomogeneousGauge ν)
    (hhom : ∀ t : ℝ, 0 < t → ∀ x, x ≠ 0 →
      F (G.dilate t x) = t ^ (-(G.homogeneousDimension : ℝ)) * F x)
    {R ε : ℝ} (hε : 0 < ε) :
    (∫ w in {w | ν w ≤ R * ε}, F w * (1 - η (G.dilate ε⁻¹ w))) =
      ∫ v in {v | ν v ≤ R}, F v * (1 - η v) := by
  have hs := integral_homogeneousBall_weighted_dilate G hν hhom
    (θ := fun v => 1 - η v) (R := R) hε
  have he : -(G.homogeneousDimension : ℝ) + (G.homogeneousDimension : ℝ) = 0 := by ring
  simpa only [he, Real.rpow_zero, one_mul] using hs

end RothschildStein.H1

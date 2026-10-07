-- Copyright (c) 2026 Scott Armstrong and Amélie Loher. All rights reserved.
-- Released under Apache 2.0 license as described in the file LICENSE.
module

public import RothschildStein.H3.TypeZeroPrincipalValueDilation
public import RothschildStein.H3.DilationRestrictedLp

set_option autoImplicit false
set_option relaxedAutoImplicit false
@[expose] public section
noncomputable section
namespace RothschildStein.H3
open MeasureTheory
open scoped ENNReal
variable {N : ℕ} (G : HomogeneousGroup N)

/-- Exact finite-ball Lp scaling of the actual type-zero principal value. -/
theorem TypeZero.principalValue_eLpNorm_dilate_sublevel {ν : G2.HomogeneousNorm G}
    {k u : (Fin N → ℝ) → ℝ} (hk : TypeZero G ν k)
    (hu : ContDiff ℝ 1 u) (hs : HasCompactSupport u) (p : ℝ≥0∞)
    (R : ℝ) {t : ℝ} (ht : 0 < t) :
    eLpNorm (H1.principalValueConvolution G ν k (fun y => u (G.dilate t y))) p
      (volume.restrict {x | ν x < R}) =
      ENNReal.ofReal ((t ^ G.homogeneousDimension)⁻¹) ^ (1 / p.toReal) *
        eLpNorm (H1.principalValueConvolution G ν k u) p
          (volume.restrict {x | ν x < t * R}) := by
  rw [hk.principalValue_dilate G hu hs ht]
  exact eLpNorm_dilate_gauge_sublevel G ν.gauge _ p R ht

end RothschildStein.H3

-- Copyright (c) 2026 Scott Armstrong and Amélie Loher. All rights reserved.
-- Released under Apache 2.0 license as described in the file LICENSE.
module

public import RothschildStein.H3.TypeZeroPrincipalValue
public import RothschildStein.H3.PrincipalValueDilation
public import RothschildStein.H3.DilationLp
public import RothschildStein.G2.TransposeHomogeneity

set_option autoImplicit false
set_option relaxedAutoImplicit false
@[expose] public section
noncomputable section
namespace RothschildStein.H3
open MeasureTheory Filter
open scoped ENNReal Topology
variable {N : ℕ} (G : HomogeneousGroup N)

/-- Type-zero principal values commute with positive dilations on C1 compact sources. -/
theorem TypeZero.principalValue_dilate {ν : G2.HomogeneousNorm G}
    {k u : (Fin N → ℝ) → ℝ} (hk : TypeZero G ν k)
    (hu : ContDiff ℝ 1 u) (hs : HasCompactSupport u) {t : ℝ} (ht : 0 < t) :
    H1.principalValueConvolution G ν k (fun y => u (G.dilate t y)) =
      fun x => H1.principalValueConvolution G ν k u (G.dilate t x) := by
  have hut : ContDiff ℝ 1 (fun y => u (G.dilate t y)) :=
    hu.comp ((G2.contDiff_dilate G t).of_le (by simp))
  have hst : HasCompactSupport (fun y => u (G.dilate t y)) :=
    hs.comp_homeomorph (G2.dilationHomeomorph G t ht)
  funext x
  have hleft := hk.hasPrincipalValue G hut hst x
  have hright := hk.hasPrincipalValue G hu hs (G.dilate t x)
  have hscaled := (hasPrincipalValue_dilation_iff G ν.gauge hk.homogeneous u x ht _).mp hleft
  exact tendsto_nhds_unique hscaled.2 hright.2

end RothschildStein.H3

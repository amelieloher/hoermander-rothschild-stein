-- Copyright (c) 2026 Scott Armstrong and Amélie Loher. All rights reserved.
-- Released under Apache 2.0 license as described in the file LICENSE.
module

public import RothschildStein.H3.TypeZeroShells
public import RothschildStein.H1.PrincipalValueExistence

set_option autoImplicit false
set_option relaxedAutoImplicit false
@[expose] public section
noncomputable section
namespace RothschildStein.H3
open Set
variable {N : ℕ} (G : HomogeneousGroup N)

/-- Every compactly supported C1 input has a principal value at every
point under the type-zero kernel bounds. -/
theorem TypeZero.hasPrincipalValue {ν : G2.HomogeneousNorm G}
    {f u : (Fin N → ℝ) → ℝ} (hf : TypeZero G ν f)
    (hu : ContDiff ℝ 1 u) (hs : HasCompactSupport u) (x : Fin N → ℝ) :
    G.HasPrincipalValue ν f u x (H1.principalValueConvolution G ν f u x) :=
  H1.hasPrincipalValue_critical_cancelled G ν.gauge hf.smooth.continuousOn
    hf.homogeneous (hf.vanishingShellIntegrals G) hu hs x

/-- The actual global principal-value representative is continuous.
This exports existence and continuity, separately from the global Lp estimate. -/
theorem TypeZero.continuous_principalValue {ν : G2.HomogeneousNorm G}
    {f u : (Fin N → ℝ) → ℝ} (hf : TypeZero G ν f)
    (hu : ContDiff ℝ 1 u) (hs : HasCompactSupport u) :
    Continuous (H1.principalValueConvolution G ν f u) :=
  H1.continuous_principalValueConvolution G ν.gauge hf.smooth.continuousOn
    hf.homogeneous hu hs

end RothschildStein.H3

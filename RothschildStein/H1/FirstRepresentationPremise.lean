-- Copyright (c) 2026 Scott Armstrong and Amélie Loher. All rights reserved.
-- Released under Apache 2.0 license as described in the file LICENSE.
module

public import RothschildStein.H1.AssemblyInputs
public import RothschildStein.H1.FundamentalFirstDerivative

set_option autoImplicit false
set_option relaxedAutoImplicit false
@[expose] public section
noncomputable section
open Set MeasureTheory
namespace RothschildStein.H1
variable {N q : ℕ} {G : HomogeneousGroup N} {H : StandingHypotheses G q}

/-- The first-derivative representation holds with absolute convergence
(BB (6.45), p. 281). -/
theorem FundamentalKernel.firstKernelRepresentation (K : FundamentalKernel G H)
    (hQ : 2 < (G.homogeneousDimension : ℝ)) : FirstKernelRepresentation K := by
  intro φ j x
  refine ⟨K.firstDerivative_integrable G H j φ.contDiff φ.hasCompactSupport x, ?_⟩
  have h := congrFun (K.firstDerivative_representation G H hQ j φ.contDiff φ.hasCompactSupport) x
  simpa only [G2.groupConvolution_eq_integral, HomogeneousGroup.potential] using h

end RothschildStein.H1

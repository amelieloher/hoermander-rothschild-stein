-- Copyright (c) 2026 Scott Armstrong and Amélie Loher. All rights reserved.
-- Released under Apache 2.0 license as described in the file LICENSE.
module

public import RothschildStein.H3.FundamentalCorrectionCoefficients
public import RothschildStein.G2.ControlMeasure
public import RothschildStein.Definitions.driftWeight

set_option autoImplicit false
set_option relaxedAutoImplicit false
@[expose] public section
noncomputable section
namespace RothschildStein.H3

/-- Choose the analytic norm in the standing data independently
of its prescribed homogeneous fields (BB Theorem 8.50, p. 379). -/
def standingWithNorm {N q : ℕ} (G : HomogeneousGroup N)
    (H : H1.StandingHypotheses G q) (ν : G2.HomogeneousNorm G) : H1.StandingHypotheses G q :=
  { H with norm := ν }

/-- A fundamental kernel transports to any choice of standing
norm: its defining properties concern the field operator (BB p. 379). -/
def fundamentalKernelWithNorm {N q : ℕ} (G : HomogeneousGroup N)
    (H : H1.StandingHypotheses G q) (ν : G2.HomogeneousNorm G)
    (K : H1.FundamentalKernel G H) : H1.FundamentalKernel G (standingWithNorm G H ν) :=
  ⟨K.toFun, K.locallyIntegrable, K.smooth_off_zero, K.homogeneous, K.fundamental⟩

/-- Fixed correction coefficients for the canonical control
norm, chosen independently of input functions and their supports. -/
def controlCorrectionCoefficients {N q : ℕ} (G : HomogeneousGroup N)
    (H : H1.StandingHypotheses G q) (K : H1.FundamentalKernel G H)
    (C : G2.ControlNormConclusion G driftWeight H.fields)
    (hQ : 2 < (G.homogeneousDimension : ℝ)) : Fin q → Fin q → ℝ :=
  fundamentalCorrectionCoefficients G (standingWithNorm G H C.norm)
    (fundamentalKernelWithNorm G H C.norm K) hQ

end RothschildStein.H3

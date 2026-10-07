-- Copyright (c) 2026 Scott Armstrong and Amélie Loher. All rights reserved.
-- Released under Apache 2.0 license as described in the file LICENSE.
module

public import RothschildStein.H3.ConvolutionFormulas

set_option autoImplicit false
set_option relaxedAutoImplicit false
@[expose] public section
noncomputable section
namespace RothschildStein.H3

/-- One finite correction family for the fundamental-kernel convolution,
chosen independently of source functions and support radii (BB Proposition
8.49 and Theorem 8.50, pp. 379–380). -/
def fundamentalCorrectionCoefficients {N q : ℕ}
    (G : HomogeneousGroup N) (H : H1.StandingHypotheses G q)
    (K : H1.FundamentalKernel G H) (hQ : 2 < (G.homogeneousDimension : ℝ)) :
    Fin q → Fin q → ℝ :=
  Classical.choose (convolution_formulas_of_fundamental_kernel G H K hQ)

end RothschildStein.H3

-- Copyright (c) 2026 Scott Armstrong and Amélie Loher. All rights reserved.
-- Released under Apache 2.0 license as described in the file LICENSE.
module

public import RothschildStein.H1.PremiseAssembly
public import RothschildStein.H1.GlobalFundamentalExistence
public import RothschildStein.H1.DistributionalInfinityUniqueness

set_option autoImplicit false
set_option relaxedAutoImplicit false
@[expose] public section
noncomputable section
namespace RothschildStein.H1
variable {N q : ℕ}

/-- Every stated fundamental-kernel property holds, including
arbitrary-distribution uniqueness (BB Theorem 11.5, pp. 538–539). -/
theorem assemble_kernel {G : HomogeneousGroup N} {H : StandingHypotheses G q}
    (K : FundamentalKernel G H) (hQ : 2 < (G.homogeneousDimension : ℝ)) :
    FundamentalKernelProperties K :=
  assemble_kernel_of_uniqueness K hQ (K.distributionalKernelUniqueness hQ)
    (K.distributionalKernelUniquenessAtInfinity hQ)

end RothschildStein.H1

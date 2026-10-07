-- Copyright (c) 2026 Scott Armstrong and Amélie Loher. All rights reserved.
-- Released under Apache 2.0 license as described in the file LICENSE.
module

public import RothschildStein.H1.KernelAssembly
public import RothschildStein.H1.KernelBoundPremises
public import RothschildStein.H1.FirstRepresentationPremise
public import RothschildStein.H1.SecondRepresentationPremise

set_option autoImplicit false
set_option relaxedAutoImplicit false
@[expose] public section
noncomputable section
open Set MeasureTheory
namespace RothschildStein.H1
variable {N q : ℕ} {G : HomogeneousGroup N} {H : StandingHypotheses G q}

/-- The kernel properties follow from the local weak regularity theorem
and uniqueness for arbitrary distributions (BB pp. 538–539). -/
theorem assemble_kernel_of_uniqueness (K : FundamentalKernel G H)
    (hQ : 2 < (G.homogeneousDimension : ℝ))
    (hUniq : DistributionalKernelUniqueness K)
    (hUniqInf : DistributionalKernelUniquenessAtInfinity K) : FundamentalKernelProperties K :=
  assemble_kernel_of_uniqueness_bounds_cancellation K hQ hUniq K.generalKernelBounds
    K.kernelShellCancellation (K.firstKernelRepresentation hQ)
    (K.secondKernelRepresentation hQ) hUniqInf

end RothschildStein.H1

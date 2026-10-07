-- Copyright (c) 2026 Scott Armstrong and Amélie Loher. All rights reserved.
-- Released under Apache 2.0 license as described in the file LICENSE.
module

public import RothschildStein.Provider.FundamentalSolutionBridges
public import RothschildStein.H1.CompleteAssembly

set_option autoImplicit false
set_option relaxedAutoImplicit false
@[expose] public section
noncomputable section
namespace RothschildStein.Provider

/-- The differential, representation, and uniqueness properties required by the
assembly follow from the fundamental-kernel properties. -/
theorem fundamentalSolutionInputs {N : ℕ} (G : HomogeneousGroup N)
    (hQ : 2 < (G.homogeneousDimension : ℝ)) : FundamentalSolutionInputs G :=
  ⟨fun H h => H.exists_globalFundamentalKernel G h,
    fun _ K => K.distributionalKernelUniqueness hQ,
    fun _ K => K.distributionalKernelUniquenessAtInfinity hQ⟩

end RothschildStein.Provider

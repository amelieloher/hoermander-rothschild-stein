-- Copyright (c) 2026 Scott Armstrong and Amélie Loher. All rights reserved.
-- Released under Apache 2.0 license as described in the file LICENSE.
module

public import RothschildStein.H3.KernelDerivativeProperties
public import RothschildStein.G2.GaugeConsequences

set_option autoImplicit false
set_option relaxedAutoImplicit false
@[expose] public section
noncomputable section
open Set
namespace RothschildStein.H3
variable {N : ℕ} (G : HomogeneousGroup N)

/-- Inversion preserves the exact zeroth-order kernel maximum
for a symmetric gauge; no regularity or cancellation is required. -/
theorem kernelSphereBound_reflection (ν : G2.HomogeneousNorm G) (hsym : ν.Symmetric)
    (T : (Fin N → ℝ) → ℝ) :
    kernelSphereBound ν (fun x => T (G.inv x)) = kernelSphereBound ν T := by
  unfold kernelSphereBound
  congr 1
  ext b
  constructor
  · rintro ⟨x, hx, rfl⟩
    exact ⟨G.inv x, (hsym x).trans hx, rfl⟩
  · rintro ⟨x, hx, rfl⟩
    refine ⟨G.inv x, (hsym x).trans hx, ?_⟩
    change |T (G.inv (G.inv x))| = |T x|
    rw [G2.inv_inv]

end RothschildStein.H3

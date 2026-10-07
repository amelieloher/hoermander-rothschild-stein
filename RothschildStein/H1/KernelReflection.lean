-- Copyright (c) 2026 Scott Armstrong and Amélie Loher. All rights reserved.
-- Released under Apache 2.0 license as described in the file LICENSE.
module

public import RothschildStein.H1.KernelData
public import RothschildStein.H1.ReflectedKernel

set_option autoImplicit false
set_option relaxedAutoImplicit false
set_option backward.isDefEq.respectTransparency false
@[expose] public section
noncomputable section
namespace RothschildStein.H1
variable {N q : ℕ} {G : HomogeneousGroup N} {H : StandingHypotheses G q}

/-- The reflected original kernel supplies the transpose kernel
without a second existence assumption (BB Theorem 11.5(e), printed p. 539).
Its arbitrary value at zero is carried along by inversion. -/
def FundamentalKernel.reflection (K : FundamentalKernel G H)
    (hQ : 2 < (G.homogeneousDimension : ℝ)) : FundamentalKernel G (H.reverseDrift G) where
  toFun := fun x => K (G.inv x)
  locallyIntegrable := locallyIntegrable_comp_inv G K.locallyIntegrable
  smooth_off_zero := contDiffOn_comp_inv_off_zero G K.smooth_off_zero
  homogeneous := homogeneous_comp_inv G K.homogeneous
  fundamental := fun _ hφ hc => H.reflected_fundamental_pairing G hQ K.locallyIntegrable
    K.smooth_off_zero K.homogeneous K.fundamental hφ hc

/-- The assembled transpose kernel is inversion reflection,
including the freely chosen representative value at zero (BB p. 539). -/
theorem FundamentalKernel.reflection_apply (K : FundamentalKernel G H)
    (hQ : 2 < (G.homogeneousDimension : ℝ)) (x : Fin N → ℝ) :
    K.reflection hQ x = K (G.inv x) := rfl

/-- Negation reflection has exactly the coordinate hypothesis
under the coordinate condition (BB p. 539). -/
theorem FundamentalKernel.reflection_neg (K : FundamentalKernel G H)
    (hQ : 2 < (G.homogeneousDimension : ℝ)) (hinv : ∀ x, G.inv x = -x) (x : Fin N → ℝ) :
    K.reflection hQ x = K (-x) := by
  rw [K.reflection_apply hQ, hinv x]

end RothschildStein.H1

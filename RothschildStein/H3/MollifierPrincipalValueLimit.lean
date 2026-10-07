-- Copyright (c) 2026 Scott Armstrong and Amélie Loher. All rights reserved.
-- Released under Apache 2.0 license as described in the file LICENSE.
module

public import RothschildStein.H3.MollifierPrincipalValueNearLimit
public import RothschildStein.H3.PrincipalValueFarKernel

set_option autoImplicit false
set_option relaxedAutoImplicit false
@[expose] public section
noncomputable section
open Set MeasureTheory Filter
open scoped Topology
namespace RothschildStein.H3

/-- Actual principal-value convolution converges under group
regularization of a compact continuous globally Hölder source.
The near and far terms are treated separately (BB Proposition 8.49). -/
theorem tendsto_principalValueConvolution_groupRegularize {N : ℕ}
    (G : HomogeneousGroup N) (ν : G2.HomogeneousNorm G) (hsym : ν.Symmetric)
    (φ : G2.GroupMollifier G ν) {K f : (Fin N → ℝ) → ℝ}
    (hK : TypeZero G ν K) (hf : Continuous f) (hc : HasCompactSupport f)
    {α H : ℝ} (hα : 0 < α)
    (hholder : ∀ x y, |f x - f y| ≤ H * (G2.gaugeDistance G ν x y) ^ α)
    (x : Fin N → ℝ) :
    Tendsto (fun ε : ℝ => H1.principalValueConvolution G ν K
      (G2.groupRegularize G φ f ε) x) (𝓝[>] 0)
      (𝓝 (H1.principalValueConvolution G ν K f x)) := by
  exact (tendsto_principalValueNear_groupRegularize G ν hsym φ hK hf hc hα hholder x).add
    (tendsto_principalValueFar_groupRegularize G φ hK.smooth.continuousOn hf hc x)

end RothschildStein.H3

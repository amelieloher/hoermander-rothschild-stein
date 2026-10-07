-- Copyright (c) 2026 Scott Armstrong and Amélie Loher. All rights reserved.
-- Released under Apache 2.0 license as described in the file LICENSE.
module

public import RothschildStein.H1.PrincipalValueNearContinuity
public import RothschildStein.H1.PrincipalValueFarContinuity

set_option autoImplicit false
set_option relaxedAutoImplicit false
@[expose] public section
noncomputable section
open Set
namespace RothschildStein.H1
variable {N : ℕ} (G : HomogeneousGroup N)

/-- The near-plus-far principal-value candidate is a
continuous function on the full carrier (BB Prop 6.29, pp. 276–278). -/
theorem continuous_principalValueConvolution
    {ν F ψ : (Fin N → ℝ) → ℝ} (hν : G.IsHomogeneousGauge ν)
    (hF : ContinuousOn F {(0 : Fin N → ℝ)}ᶜ)
    (hhom : ∀ t : ℝ, 0 < t → ∀ x, x ≠ 0 →
      F (G.dilate t x) = t ^ (-(G.homogeneousDimension : ℝ)) * F x)
    (hc : ContDiff ℝ 1 ψ) (hs : HasCompactSupport ψ) :
    Continuous (principalValueConvolution G ν F ψ) :=
  (continuous_principalValue_near G hν hF hhom hc hs).add
    (continuous_principalValue_far G hν hF hhom hc.continuous hs)

end RothschildStein.H1

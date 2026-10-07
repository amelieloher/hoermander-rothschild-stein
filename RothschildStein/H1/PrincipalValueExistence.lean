-- Copyright (c) 2026 Scott Armstrong and Amélie Loher. All rights reserved.
-- Released under Apache 2.0 license as described in the file LICENSE.
module

public import RothschildStein.H1.PrincipalValueUniformLimit
public import RothschildStein.H1.PrincipalValueSubstitution
public import RothschildStein.H1.PrincipalValueContinuity

set_option autoImplicit false
set_option relaxedAutoImplicit false
@[expose] public section
noncomputable section
open Set Filter Topology
namespace RothschildStein.H1
variable {N : ℕ} (G : HomogeneousGroup N)

/-- The continuous subtracted candidate satisfies the
first-formula principal-value condition at every point. -/
theorem hasPrincipalValue_critical_cancelled
    {ν F ψ : (Fin N → ℝ) → ℝ} (hν : G.IsHomogeneousGauge ν)
    (hF : ContinuousOn F {(0 : Fin N → ℝ)}ᶜ)
    (hhom : ∀ t : ℝ, 0 < t → ∀ x, x ≠ 0 →
      F (G.dilate t x) = t ^ (-(G.homogeneousDimension : ℝ)) * F x)
    (hcancel : HasVanishingShellIntegrals ν F)
    (hc : ContDiff ℝ 1 ψ) (hs : HasCompactSupport ψ) (x : Fin N → ℝ) :
    G.HasPrincipalValue ν F ψ x (principalValueConvolution G ν F ψ x) := by
  constructor
  · intro ε hε
    exact integrableOn_principalValue_firstTruncation G hν hF hc.continuous hs hε x
  · have ht := (tendstoUniformly_principalValueTruncation G hν hF hhom hcancel hc hs).tendsto_at x
    simpa only [principalValue_firstTruncation_eq G hν] using ht

end RothschildStein.H1

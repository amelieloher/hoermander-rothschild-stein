-- Copyright (c) 2026 Scott Armstrong and Amélie Loher. All rights reserved.
-- Released under Apache 2.0 license as described in the file LICENSE.
module

public import RothschildStein.H1.HomogeneousFieldKernelRegularity
public import RothschildStein.H1.FieldShellCancellation
public import RothschildStein.H1.PrincipalValueExistence

set_option autoImplicit false
set_option relaxedAutoImplicit false
@[expose] public section
noncomputable section
namespace RothschildStein.H1
variable {N q : ℕ} (G : HomogeneousGroup N)

/-- The principal value of an actual horizontal
kernel derivative is continuous and everywhere defined, with shell
cancellation proved from C¹ regularity of the complementary-degree
kernel. No cancellation assumption is imposed on the conclusion. -/
theorem StandingHypotheses.horizontalKernel_principalValue
    (H : StandingHypotheses G q) (i : Fin q)
    {ν f ψ : (Fin N → ℝ) → ℝ} (hν : G.IsHomogeneousGauge ν)
    (hf : ContDiffOn ℝ 1 f {(0 : Fin N → ℝ)}ᶜ)
    (hhom : ∀ t : ℝ, 0 < t → ∀ x, x ≠ 0 →
      f (G.dilate t x) = t ^ (1 - (G.homogeneousDimension : ℝ)) * f x)
    (hc : ContDiff ℝ 1 ψ) (hs : HasCompactSupport ψ) :
    Continuous (principalValueConvolution G ν (fieldDerivative (H.fields i.succ) f) ψ) ∧
    ∀ x, G.HasPrincipalValue ν (fieldDerivative (H.fields i.succ) f) ψ x
      (principalValueConvolution G ν (fieldDerivative (H.fields i.succ) f) ψ x) := by
  obtain ⟨hF, hh⟩ := H.horizontalKernel_regular G i hf hhom
  have hd : (1 - (G.homogeneousDimension : ℝ)) - 1 = -(G.homogeneousDimension : ℝ) := by ring
  have hscale : ∀ t : ℝ, 0 < t → ∀ x, x ≠ 0 →
      fieldDerivative (H.fields i.succ) f (G.dilate t x) =
        t ^ (-(G.homogeneousDimension : ℝ)) * fieldDerivative (H.fields i.succ) f x := by
    simpa only [hd] using hh
  have hcancel := H.vanishingShellIntegrals_fieldDerivative G i.succ hν hf (by simpa using hhom)
  exact ⟨continuous_principalValueConvolution G hν hF hscale hc hs,
    hasPrincipalValue_critical_cancelled G hν hF hscale hcancel hc hs⟩

end RothschildStein.H1

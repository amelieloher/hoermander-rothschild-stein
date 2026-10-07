-- Copyright (c) 2026 Scott Armstrong and Amélie Loher. All rights reserved.
-- Released under Apache 2.0 license as described in the file LICENSE.
module

public import RothschildStein.H1.GlobalFundamentalConstruction
public import RothschildStein.H1.LocalCorrectionConstruction

set_option autoImplicit false
set_option relaxedAutoImplicit false
@[expose] public section
noncomputable section
open Set MeasureTheory Filter
open scoped Topology
namespace RothschildStein.H1
variable {N q : ℕ} (G : HomogeneousGroup N)

/-- The local kernel hypotheses suffice to construct the global
homogeneous fundamental function. The compact smooth correction follows
from the weak regularity theorem, without an additional smoothness
assumption (BB pp. 265–266). -/
theorem StandingHypotheses.exists_globalFundamental_of_localKernel
    (H : StandingHypotheses G q) (hQ : 2 < (G.homogeneousDimension : ℝ))
    {Γ E : (Fin N → ℝ) → ℝ} (hΓ : LocallyIntegrable Γ)
    (hsΓ : HasCompactSupport Γ)
    (hc : ContDiffOn ℝ (⊤ : ℕ∞) Γ ({(0 : Fin N → ℝ)}ᶜ))
    (hsmE : ContDiff ℝ (⊤ : ℕ∞) E) (_hsE : HasCompactSupport E)
    (hE : E =ᶠ[𝓝 (0 : Fin N → ℝ)] 0)
    (hlocal : ∀ φ : (Fin N → ℝ) → ℝ, ContDiff ℝ (⊤ : ℕ∞) φ → HasCompactSupport φ →
      (∫ x, Γ x * sumSquaresWithDriftTranspose H.fields φ x) = φ 0 + ∫ x, E x * φ x) :
    ∃ F : (Fin N → ℝ) → ℝ,
      LocallyIntegrable F ∧ ContDiffOn ℝ (⊤ : ℕ∞) F ({(0 : Fin N → ℝ)}ᶜ) ∧
      (∀ φ : (Fin N → ℝ) → ℝ, ContDiff ℝ (⊤ : ℕ∞) φ → HasCompactSupport φ →
        (∫ x, F x * sumSquaresWithDriftTranspose H.fields φ x) = φ 0) ∧
      (∀ t : ℝ, 0 < t → ∀ x, x ≠ 0 →
        F (G.dilate t x) = t ^ (2 - (G.homogeneousDimension : ℝ)) * F x) := by
  obtain ⟨ω, hsm, hs, he⟩ := H.exists_localSmoothCorrection G hΓ hsΓ hc.continuousOn hsmE hlocal
  exact H.exists_globalFundamental_of_localCorrection G hQ hΓ hc hsm hs he hE hlocal

end RothschildStein.H1

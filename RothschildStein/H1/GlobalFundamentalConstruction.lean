-- Copyright (c) 2026 Scott Armstrong and Amélie Loher. All rights reserved.
-- Released under Apache 2.0 license as described in the file LICENSE.
module

public import RothschildStein.H1.DyadicFundamentalIdentity
public import RothschildStein.H1.FullHomogeneity

set_option autoImplicit false
set_option relaxedAutoImplicit false
@[expose] public section
noncomputable section
open Set MeasureTheory Filter
open scoped Topology
namespace RothschildStein.H1
variable {N q : ℕ} (G : HomogeneousGroup N)

/-- From the complete local scaled pairing identity and
its compact smooth correction representative, construct the global
locally integrable fundamental kernel with full positive homogeneity.
The construction starts from the local kernel and its compact smooth correction
(BB pp. 265–266). -/
theorem StandingHypotheses.exists_globalFundamental_of_localCorrection
    (H : StandingHypotheses G q) (hQ : 2 < (G.homogeneousDimension : ℝ))
    {Γ E ω : (Fin N → ℝ) → ℝ} (hΓ : LocallyIntegrable Γ)
    (hc : ContDiffOn ℝ (⊤ : ℕ∞) Γ ({(0 : Fin N → ℝ)}ᶜ))
    (hsm : ContDiff ℝ (⊤ : ℕ∞) ω) (hs : HasCompactSupport ω)
    (hω : ∀ x ≠ 0, ω x = scaledFundamentalKernel G 2 Γ x - Γ x)
    (hE : E =ᶠ[𝓝 (0 : Fin N → ℝ)] 0)
    (hlocal : ∀ φ : (Fin N → ℝ) → ℝ, ContDiff ℝ (⊤ : ℕ∞) φ → HasCompactSupport φ →
      (∫ x, Γ x * sumSquaresWithDriftTranspose H.fields φ x) = φ 0 + ∫ x, E x * φ x) :
    ∃ F : (Fin N → ℝ) → ℝ,
      LocallyIntegrable F ∧ ContDiffOn ℝ (⊤ : ℕ∞) F ({(0 : Fin N → ℝ)}ᶜ) ∧
      (∀ φ : (Fin N → ℝ) → ℝ, ContDiff ℝ (⊤ : ℕ∞) φ → HasCompactSupport φ →
        (∫ x, F x * sumSquaresWithDriftTranspose H.fields φ x) = φ 0) ∧
      (∀ t : ℝ, 0 < t → ∀ x, x ≠ 0 →
        F (G.dilate t x) = t ^ (2 - (G.homogeneousDimension : ℝ)) * F x) := by
  let F := fundamentalDyadicLimit G Γ ω
  have hi : LocallyIntegrable F := locallyIntegrable_fundamentalDyadicLimit G hQ hΓ hsm hs
  have hd : ContDiffOn ℝ (⊤ : ℕ∞) F ({(0 : Fin N → ℝ)}ᶜ) :=
    contDiffOn_fundamentalDyadicLimit G hQ hc hsm hs
  have he : ∀ φ : (Fin N → ℝ) → ℝ, ContDiff ℝ (⊤ : ℕ∞) φ → HasCompactSupport φ →
      (∫ x, F x * sumSquaresWithDriftTranspose H.fields φ x) = φ 0 :=
    H.fundamentalDyadicLimit_pairing G hQ hΓ hsm hs hω hE hlocal
  refine ⟨F, hi, hd, he, ?_⟩
  intro t ht x hx
  exact H.fundamental_fullHomogeneity G hQ hi hd
    (fun y hy => fundamentalDyadicLimit_dyadic G hQ hsm hs hω hy) he ht x hx

end RothschildStein.H1

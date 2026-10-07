-- Copyright (c) 2026 Scott Armstrong and Amélie Loher. All rights reserved.
-- Released under Apache 2.0 license as described in the file LICENSE.
module

public import RothschildStein.H1.PrincipalValueUniformLimit
public import RothschildStein.H1.InverseTestPairing

set_option autoImplicit false
set_option relaxedAutoImplicit false
@[expose] public section
noncomputable section
open Set MeasureTheory Filter Topology
namespace RothschildStein.H1
variable {N : ℕ} (G : HomogeneousGroup N)

/-- Scalar critical truncations tend to that exact
principal-value pairing. -/
theorem tendsto_scalarPrincipalValue
    {ν F φ : (Fin N → ℝ) → ℝ} (hν : G.IsHomogeneousGauge ν)
    (hF : ContinuousOn F {(0 : Fin N → ℝ)}ᶜ)
    (hhom : ∀ t : ℝ, 0 < t → ∀ x, x ≠ 0 →
      F (G.dilate t x) = t ^ (-(G.homogeneousDimension : ℝ)) * F x)
    (hcancel : HasVanishingShellIntegrals ν F)
    (hcφ : ContDiff ℝ (⊤ : ℕ∞) φ) (hsφ : HasCompactSupport φ) :
    Tendsto (fun ε : ℝ => ∫ w in {w | ε < ν w}, F w * φ w)
      (nhdsWithin 0 (Ioi 0)) (𝓝 (principalValueConvolution G ν F (φ ∘ G.inv) 0)) := by
  obtain ⟨hcψ, hsψ⟩ := compactSmooth_comp_inv G hcφ hsφ
  have ht := (tendstoUniformly_principalValueTruncation G hν hF hhom hcancel
    (hcψ.of_le (by simp)) hsψ).tendsto_at (0 : Fin N → ℝ)
  simpa only [principalValueTruncation, Function.comp_apply, G2.zero_mul, G2.inv_inv] using ht

end RothschildStein.H1

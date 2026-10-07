-- Copyright (c) 2026 Scott Armstrong and Amélie Loher. All rights reserved.
-- Released under Apache 2.0 license as described in the file LICENSE.
module

public import RothschildStein.H1.InverseTestPairing
public import RothschildStein.H1.RegularizedPotentialUniformLimit
public import RothschildStein.H1.CriticalRegularizedPotentialLimit
public import RothschildStein.H1.CriticalFieldCutoffTerm
public import RothschildStein.H1.SupercriticalFieldCutoffTerm

set_option autoImplicit false
set_option relaxedAutoImplicit false
set_option backward.isDefEq.respectTransparency false
@[expose] public section
noncomputable section
open Set MeasureTheory Filter Topology
namespace RothschildStein.H1
variable {N : ℕ} (G : HomogeneousGroup N)

/-- Critical scalar regularized pairings converge to
principal value at the identity plus the actual cutoff moment. -/
theorem tendsto_criticalRegularizedKernel_pairing
    {ν F η φ : (Fin N → ℝ) → ℝ} (hν : G.IsHomogeneousGauge ν)
    (hF : ContinuousOn F {(0 : Fin N → ℝ)}ᶜ)
    (hhom : ∀ t : ℝ, 0 < t → ∀ x, x ≠ 0 →
      F (G.dilate t x) = t ^ (-(G.homogeneousDimension : ℝ)) * F x)
    (hcancel : HasVanishingShellIntegrals ν F)
    (hη : Continuous η) (heη : η =ᶠ[𝓝 (0 : Fin N → ℝ)] fun _ => 1)
    {R : ℝ} (hR : 0 < R) (hout : ∀ w, R ≤ ν w → η w = 0) (hbη : ∀ w, ‖η w‖ ≤ 1)
    (hcφ : ContDiff ℝ (⊤ : ℕ∞) φ) (hsφ : HasCompactSupport φ) :
    Tendsto (fun ε : ℝ => ∫ w, (F w * (1 - η (G.dilate ε⁻¹ w))) * φ w)
      (nhdsWithin 0 (Ioi 0))
      (𝓝 (principalValueConvolution G ν F (φ ∘ G.inv) 0 +
        φ 0 * (∫ v in {v | ν v ≤ R}, F v * (1 - η v)))) := by
  obtain ⟨hcψ, hsψ⟩ := compactSmooth_comp_inv G hcφ hsφ
  have ht := (tendstoUniformly_criticalRegularizedPotential G hν hF hhom hcancel hη heη hR hout hbη
    (hcψ.of_le (by simp)) hsψ).tendsto_at (0 : Fin N → ℝ)
  simpa only [groupConvolution_invertedTest_zero, Function.comp_apply, G2.inv_zero] using ht

end RothschildStein.H1

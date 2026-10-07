-- Copyright (c) 2026 Scott Armstrong and Amélie Loher. All rights reserved.
-- Released under Apache 2.0 license as described in the file LICENSE.
module

public import RothschildStein.P1.RadialCutoffMoment
public import RothschildStein.H1.ScalarRegularizationLimit

set_option autoImplicit false
set_option relaxedAutoImplicit false
@[expose] public section
noncomputable section
open Set MeasureTheory Filter
open scoped Topology
namespace RothschildStein.P1
variable {N : ℕ}

/-- Smooth radial regularization converges to the
actual critical principal value, with no residual radial cutoff moment.
This provides sharp/smooth agreement once shell cancellation is established. -/
theorem tendsto_radialCritical_scalar (G : HomogeneousGroup N)
    {ν κ : (Fin N → ℝ) → ℝ} (hν : G.IsHomogeneousGauge ν)
    (hκ : ContinuousOn κ {(0 : Fin N → ℝ)}ᶜ)
    (hh : ∀ t : ℝ, 0 < t → ∀ u, u ≠ 0 →
      κ (G.dilate t u) = t ^ (-(G.homogeneousDimension : ℝ)) * κ u)
    (hc : H1.HasVanishingShellIntegrals ν κ)
    (Φ : ℝ → ℝ) (hΦ : Continuous Φ) {r R : ℝ}
    (hr : 0 < r) (hrR : r < R)
    (hone : ∀ t : ℝ, t < r → Φ t = 1)
    (hout : ∀ t : ℝ, R ≤ t → Φ t = 0)
    (hb : ∀ u, ‖Φ (ν u)‖ ≤ 1)
    (φ : (Fin N → ℝ) → ℝ) (hφ : ContDiff ℝ (⊤ : ℕ∞) φ)
    (hsφ : HasCompactSupport φ) :
    Tendsto (fun ε : ℝ => ∫ u, (κ u * (1 - Φ (ν (G.dilate ε⁻¹ u)))) * φ u)
      (𝓝[>] (0 : ℝ))
      (𝓝 (H1.principalValueConvolution G ν κ (φ ∘ G.inv) 0)) := by
  have hz : ν (0 : Fin N → ℝ) = 0 := (hν.2.2.1 0).mpr rfl
  have he : (fun u => Φ (ν u)) =ᶠ[𝓝 (0 : Fin N → ℝ)] fun _ => 1 := by
    have hn : ∀ᶠ u in 𝓝 (0 : Fin N → ℝ), ν u < r :=
      hν.1.continuousAt.eventually (gt_mem_nhds (by simpa only [hz] using hr))
    filter_upwards [hn] with u hu
    exact hone _ hu
  have ht := H1.tendsto_criticalRegularizedKernel_pairing G hν hκ hh hc
    (hΦ.comp hν.1) he (hr.trans hrR) (fun u hu => hout _ hu) hb hφ hsφ
  have hm := integral_radialCutoffMoment_zero G hν hκ hc Φ hr hrR hΦ.continuousOn hone
  simpa only [Function.comp_apply, hm, mul_zero, add_zero] using ht

end RothschildStein.P1

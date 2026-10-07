-- Copyright (c) 2026 Scott Armstrong and Amélie Loher. All rights reserved.
-- Released under Apache 2.0 license as described in the file LICENSE.
module

public import RothschildStein.H1.RadialShellIntervals
public import RothschildStein.H1.RadialWeightIntegral

set_option autoImplicit false
set_option relaxedAutoImplicit false
@[expose] public section
noncomputable section
open Set MeasureTheory
namespace RothschildStein.H1
variable {N : ℕ} (G : HomogeneousGroup N)

/-- Every continuous radial weight preserves cancellation
on a shell (BB Proposition 6.28, pp. 275–276). -/
theorem integral_gaugeShell_radialWeight_zero
    {ν f : (Fin N → ℝ) → ℝ} (hν : G.IsHomogeneousGauge ν)
    (hc : ContinuousOn f {(0 : Fin N → ℝ)}ᶜ)
    (he : HasVanishingShellIntegrals ν f)
    {r R : ℝ} (hr : 0 < r) (hrR : r < R)
    {Φ : ℝ → ℝ} (hΦ : ContinuousOn Φ (Icc r R)) :
    ∫ x in gaugeShell ν r R, f x * Φ (ν x) = 0 := by
  let κ : ℝ → ℝ := fun t => max r (min R t)
  have hk : Continuous κ := continuous_const.max (continuous_const.min continuous_id)
  have hkr (t : ℝ) : κ t ∈ Icc r R :=
    ⟨le_max_left _ _, max_le hrR.le (min_le_left _ _)⟩
  have hg : Continuous (Φ ∘ κ) := hΦ.comp_continuous hk hkr
  obtain ⟨C, hC⟩ := (isCompact_Icc.image_of_continuousOn hΦ).isBounded.exists_norm_le
  have hb (t : ℝ) : ‖(Φ ∘ κ) t‖ ≤ C := hC _ ⟨κ t, hkr t, rfl⟩
  have hi : Integrable ((gaugeShell ν r R).indicator f) :=
    (integrable_indicator_iff (measurableSet_gaugeShell hν r R)).mpr
      (integrableOn_gaugeShell hν hc hr)
  have hz := integral_radialWeight_zero hi hν.1.measurable
    (integral_shellIndicator_gaugeInterval_zero G hν he hr) hg.measurable hb
  have hp : (fun x => (gaugeShell ν r R).indicator f x * (Φ ∘ κ) (ν x)) =
      (gaugeShell ν r R).indicator (fun x => f x * Φ (ν x)) := by
    funext x
    by_cases hx : x ∈ gaugeShell ν r R
    · rw [indicator_of_mem hx, indicator_of_mem hx]
      simp only [Function.comp_apply, κ, min_eq_right hx.2, max_eq_right hx.1]
    · rw [indicator_of_notMem hx, indicator_of_notMem hx, zero_mul]
  rw [hp, integral_indicator (measurableSet_gaugeShell hν r R)] at hz
  exact hz

end RothschildStein.H1

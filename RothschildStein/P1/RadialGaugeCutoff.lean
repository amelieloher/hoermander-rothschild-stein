-- Copyright (c) 2026 Scott Armstrong and Amélie Loher. All rights reserved.
-- Released under Apache 2.0 license as described in the file LICENSE.
module

public import RothschildStein.G2.Gauge
public import Mathlib.Analysis.SpecialFunctions.SmoothTransition

set_option autoImplicit false
set_option relaxedAutoImplicit false
@[expose] public section
noncomputable section
open Set Filter
open scoped Topology
namespace RothschildStein.P1
variable {N : ℕ} {G : HomogeneousGroup N}

/-- A fixed smooth radial profile, equal to one
below radius one and zero above radius two. -/
def radialCutoffProfile (r : ℝ) : ℝ := Real.smoothTransition (2 - r)

theorem radialCutoffProfile_contDiff : ContDiff ℝ (⊤ : ℕ∞) radialCutoffProfile :=
  Real.smoothTransition.contDiff.comp (contDiff_const.sub contDiff_id)

theorem radialCutoffProfile_one {r : ℝ} (hr : r ≤ 1) : radialCutoffProfile r = 1 :=
  Real.smoothTransition.one_of_one_le (by linarith)

theorem radialCutoffProfile_zero {r : ℝ} (hr : 2 ≤ r) : radialCutoffProfile r = 0 :=
  Real.smoothTransition.zero_of_nonpos (by linarith)

theorem radialCutoffProfile_norm_le (r : ℝ) : ‖radialCutoffProfile r‖ ≤ 1 := by
  change ‖Real.smoothTransition (2 - r)‖ ≤ 1
  rw [Real.norm_eq_abs, abs_of_nonneg (Real.smoothTransition.nonneg (2 - r))]
  exact Real.smoothTransition.le_one _

/-- The prescribed-gauge radial cutoff equals one
on a neighborhood of the pole. -/
theorem radialGaugeCutoff_eventually_one {ν : (Fin N → ℝ) → ℝ}
    (hν : G.IsHomogeneousGauge ν) :
    (fun u => radialCutoffProfile (ν u)) =ᶠ[𝓝 (0 : Fin N → ℝ)] fun _ => 1 := by
  have hz : ν (0 : Fin N → ℝ) = 0 := (hν.2.2.1 0).mpr rfl
  have hn : ∀ᶠ u in 𝓝 (0 : Fin N → ℝ), ν u < 1 :=
    hν.1.continuousAt.eventually (gt_mem_nhds (by rw [hz]; exact zero_lt_one))
  exact hn.mono (fun _ hu => radialCutoffProfile_one hu.le)

/-- Smoothness at the pole follows from the plateau,
so the prescribed gauge need only be smooth off zero. -/
theorem radialGaugeCutoff_contDiff {ν : (Fin N → ℝ) → ℝ}
    (hν : G.IsHomogeneousGauge ν)
    (hsν : ContDiffOn ℝ (⊤ : ℕ∞) ν {(0 : Fin N → ℝ)}ᶜ) :
    ContDiff ℝ (⊤ : ℕ∞) (fun u => radialCutoffProfile (ν u)) := by
  rw [contDiff_iff_contDiffAt]
  intro u
  by_cases hu : u = 0
  · subst u
    exact contDiffAt_const.congr_of_eventuallyEq (radialGaugeCutoff_eventually_one hν)
  · exact radialCutoffProfile_contDiff.contDiffAt.comp u
      (hsν.contDiffAt (isOpen_compl_singleton.mem_nhds hu))

/-- The radial cutoff has compact support in the
closed prescribed-gauge ball of radius two. -/
theorem radialGaugeCutoff_hasCompactSupport {ν : (Fin N → ℝ) → ℝ}
    (hν : G.IsHomogeneousGauge ν) :
    HasCompactSupport (fun u => radialCutoffProfile (ν u)) := by
  apply HasCompactSupport.of_support_subset_isCompact (G2.isCompact_gauge_le hν 2)
  intro u hu
  by_contra hn
  exact hu (radialCutoffProfile_zero (le_of_not_ge hn))

end RothschildStein.P1

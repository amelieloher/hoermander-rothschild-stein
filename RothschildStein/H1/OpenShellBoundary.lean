-- Copyright (c) 2026 Scott Armstrong and Amélie Loher. All rights reserved.
-- Released under Apache 2.0 license as described in the file LICENSE.
module

public import RothschildStein.H1.ShellGeometry

set_option autoImplicit false
set_option relaxedAutoImplicit false
@[expose] public section
noncomputable section
open Set MeasureTheory Filter
namespace RothschildStein.H1
variable {N : ℕ} (G : HomogeneousGroup N)

/-- Strict shells and closed shells agree almost
everywhere, because each positive gauge level has zero volume. -/
theorem openGaugeShell_ae_eq_closed {ν : (Fin N → ℝ) → ℝ}
    (hν : G.IsHomogeneousGauge ν) {r R : ℝ} (hr : 0 < r) (hR : 0 < R) :
    {x | r < ν x ∧ ν x < R} =ᵐ[volume] gaugeShell ν r R := by
  filter_upwards [ae_gauge_ne G hν hr, ae_gauge_ne G hν hR] with x hxr hxR
  apply propext
  change (r < ν x ∧ ν x < R) ↔ (r ≤ ν x ∧ ν x ≤ R)
  exact ⟨fun h => ⟨h.1.le, h.2.le⟩,
    fun h => ⟨lt_of_le_of_ne h.1 hxr.symm, lt_of_le_of_ne h.2 hxR⟩⟩

/-- The strict-shell integral equals the shell integral
used by the cancellation API, without extra integrability premises. -/
theorem integral_openGaugeShell_eq_closed {ν f : (Fin N → ℝ) → ℝ}
    (hν : G.IsHomogeneousGauge ν) {r R : ℝ} (hr : 0 < r) (hR : 0 < R) :
    (∫ x in {x | r < ν x ∧ ν x < R}, f x) = ∫ x in gaugeShell ν r R, f x :=
  setIntegral_congr_set (openGaugeShell_ae_eq_closed G hν hr hR)

end RothschildStein.H1

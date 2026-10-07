-- Copyright (c) 2026 Scott Armstrong and Amélie Loher. All rights reserved.
-- Released under Apache 2.0 license as described in the file LICENSE.
module

public import RothschildStein.P1.RadialGaugeCutoff
public import Mathlib.MeasureTheory.Integral.Bochner.Basic

set_option autoImplicit false
set_option relaxedAutoImplicit false
@[expose] public section
noncomputable section
open Set MeasureTheory
namespace RothschildStein.P1
variable {N : ℕ}

/-- A smooth radial cutoff integral is
controlled by the absolute row mass in its actual radius-2ε support. -/
theorem norm_radialCutoff_integral_le (G : HomogeneousGroup N)
    {ν : (Fin N → ℝ) → ℝ} (hν : G.IsHomogeneousGauge ν)
    {f : (Fin N → ℝ) → ℝ} (hi : Integrable f)
    {ε : ℝ} (hε : 0 < ε) :
    ‖∫ u, radialCutoffProfile (ν (G.dilate ε⁻¹ u)) * f u‖ ≤
      ∫ u in {u | ν u ≤ 2 * ε}, ‖f u‖ := by
  let A := {u : Fin N → ℝ | ν u ≤ 2 * ε}
  have hA : MeasurableSet A := (isClosed_le hν.1 continuous_const).measurableSet
  have hdom : ∀ u, ‖radialCutoffProfile (ν (G.dilate ε⁻¹ u)) * f u‖ ≤
      A.indicator (fun v => ‖f v‖) u := by
    intro u
    by_cases hu : u ∈ A
    · rw [indicator_of_mem hu, norm_mul]
      simpa only [one_mul] using mul_le_mul_of_nonneg_right
        (radialCutoffProfile_norm_le _) (norm_nonneg (f u))
    · have hlarge : 2 ≤ ν (G.dilate ε⁻¹ u) := by
        rw [hν.2.2.2 ε⁻¹ (inv_pos.mpr hε)]
        have hh : 2 * ε < ν u := not_le.mp hu
        have hdiv : 2 ≤ ν u / ε := (le_div_iff₀ hε).mpr hh.le
        simpa only [div_eq_mul_inv, mul_comm] using hdiv
      rw [radialCutoffProfile_zero hlarge, zero_mul, norm_zero, indicator_of_notMem hu]
  have hb := norm_integral_le_of_norm_le (hi.norm.indicator hA)
    (Filter.Eventually.of_forall hdom)
  rw [integral_indicator hA] at hb
  exact hb

end RothschildStein.P1

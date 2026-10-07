-- Copyright (c) 2026 Scott Armstrong and Amélie Loher. All rights reserved.
-- Released under Apache 2.0 license as described in the file LICENSE.
module

public import RothschildStein.H1.LogShellContinuity
public import RothschildStein.H1.PositiveCauchy

set_option autoImplicit false
set_option relaxedAutoImplicit false
@[expose] public section
noncomputable section
open Set MeasureTheory
namespace RothschildStein.H1
variable {N : ℕ} (G : HomogeneousGroup N)

/-- The critical shell integral is the exactly normalized
mean times log(R/r) (BB Proposition 6.26(2), (6.38), p. 274). -/
theorem integral_gaugeShell_eq_mean_mul_log
    {ν f : (Fin N → ℝ) → ℝ} (hν : G.IsHomogeneousGauge ν)
    (hc : ContinuousOn f {(0 : Fin N → ℝ)}ᶜ)
    (hf : ∀ t : ℝ, 0 < t → ∀ x, x ≠ 0 →
      f (G.dilate t x) = t ^ (-(G.homogeneousDimension : ℝ)) * f x)
    {r R : ℝ} (hr : 0 < r) (hrR : r < R) :
    (∫ x in gaugeShell ν r R, f x) = homogeneousShellMean ν f * Real.log (R / r) := by
  have hratio : 1 < R / r := (lt_div_iff₀ hr).mpr (by simpa only [one_mul] using hrR)
  have hratio0 : 0 < R / r := zero_lt_one.trans hratio
  have hlog : 0 ≤ Real.log (R / r) := (Real.log_pos hratio).le
  have hlinear := nonneg_additive_eq_mul (logShellPrimitive_zero G hν (f := f))
    (fun a b ha hb => logShellPrimitive_add_nonneg G hν hc hf ha hb)
    (continuousWithinAt_logShellPrimitive_zero G hν hc) (Real.log (R / r)) hlog
  have hs := integral_gaugeShell_scale G hν hf (r := 1) (R := R / r)
    (by norm_num) hr
  have he : r * (R / r) = R := by field_simp
  rw [mul_one, he] at hs
  rw [hs]
  have hleft : logShellPrimitive ν f (Real.log (R / r)) =
      ∫ x in gaugeShell ν 1 (R / r), f x := by
    rw [logShellPrimitive, Real.exp_log hratio0]
  rw [hleft] at hlinear
  rw [hlinear]
  change Real.log (R / r) * homogeneousShellMean ν f = _
  ring

end RothschildStein.H1

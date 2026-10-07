-- Copyright (c) 2026 Scott Armstrong and Amélie Loher. All rights reserved.
-- Released under Apache 2.0 license as described in the file LICENSE.
module

public import RothschildStein.H2.Marcinkiewicz

@[expose] public section

set_option autoImplicit false
set_option relaxedAutoImplicit false

noncomputable section

open Set MeasureTheory
open scoped ENNReal NNReal

namespace RothschildStein.H2

variable {Y Z : Type*} [MeasurableSpace Y] [MeasurableSpace Z]

/-- The Lᵖ norm is the p-th root of the moment used in the interpolation
proof (BB Thm 7.48, pp. 334–335). -/
theorem eLpNorm_eq_moment_rpow (ν : Measure Y) {f : Y → ℝ}
    (hf : AEMeasurable f ν) {p : ℝ} (hp : 0 < p) :
    eLpNorm f (ENNReal.ofReal p) ν = moment ν p f ^ (1 / p) := by
  rw [eLpNorm_eq_lintegral_rpow_enorm_toReal (by positivity) ENNReal.ofReal_ne_top
    hf.aestronglyMeasurable, ENNReal.toReal_ofReal hp.le]
  congr 1
  apply lintegral_congr
  intro y
  rw [← ofReal_norm, Real.norm_eq_abs,
    ENNReal.ofReal_rpow_of_nonneg (abs_nonneg _) hp.le]

/-- Membership in Lᵖ is equivalent to a finite moment for a measurable
real function (BB Thm 7.48, pp. 334–335). -/
theorem memLp_iff_moment_lt_top (ν : Measure Y) {f : Y → ℝ}
    (hf : AEMeasurable f ν) {p : ℝ} (hp : 0 < p) :
    MemLp f (ENNReal.ofReal p) ν ↔ moment ν p f < ∞ := by
  rw [MemLp, eLpNorm_eq_moment_rpow ν hf hp]
  exact ENNReal.rpow_lt_top_iff_of_pos (by positivity)

/-- A power-moment interpolation bound gives the norm bound, with the
p-th root of the exact constant (BB Thm 7.48, pp. 334–335). -/
theorem eLpNorm_le_of_moment_le
    (ν : Measure Y) (μout : Measure Z) {f : Y → ℝ} {F : Z → ℝ}
    (hf : AEMeasurable f ν) (hF : AEMeasurable F μout) {p C : ℝ} (hp : 0 < p)
    (hbound : moment μout p F ≤ ENNReal.ofReal C * moment ν p f) :
    eLpNorm F (ENNReal.ofReal p) μout ≤
      ENNReal.ofReal C ^ (1 / p) * eLpNorm f (ENNReal.ofReal p) ν := by
  rw [eLpNorm_eq_moment_rpow ν hf hp, eLpNorm_eq_moment_rpow μout hF hp,
    ← ENNReal.mul_rpow_of_nonneg _ _ (by positivity : 0 ≤ 1 / p)]
  exact ENNReal.rpow_le_rpow hbound (by positivity)

/-- A finite input moment and a finite interpolation constant give an
Lᵖ output, not just a formal extended-norm inequality (BB Thm 7.48, pp. 334–335). -/
theorem memLp_of_moment_bound
    (ν : Measure Y) (μout : Measure Z) {f : Y → ℝ} {F : Z → ℝ}
    (hF : AEMeasurable F μout) {p C : ℝ} (hp : 0 < p)
    (hfin : moment ν p f < ∞)
    (hbound : moment μout p F ≤ ENNReal.ofReal C * moment ν p f) :
    MemLp F (ENNReal.ofReal p) μout := by
  rw [memLp_iff_moment_lt_top μout hF hp]
  exact hbound.trans_lt (ENNReal.mul_lt_top ENNReal.ofReal_lt_top hfin)

/-- Chebyshev for extended power moments, retaining possible infinity
values (BB Lemma 7.26, p. 314). -/
theorem chebyshev_ennreal_power (ν : Measure Y) {F : Y → ℝ≥0∞}
    (hF : AEMeasurable F ν) {p s : ℝ} (hp : 0 < p) (hs : 0 < s) :
    ENNReal.ofReal (s ^ p) * ν {y | ENNReal.ofReal s ≤ F y} ≤ ∫⁻ y, F y ^ p ∂ν := by
  rw [← ENNReal.ofReal_rpow_of_pos hs]
  apply le_trans (mul_le_mul' le_rfl (measure_mono ?_))
    (mul_meas_ge_le_lintegral₀ (hF.pow_const p) (ENNReal.ofReal s ^ p))
  intro y hy
  exact ENNReal.rpow_le_rpow hy hp.le

end RothschildStein.H2

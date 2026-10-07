-- Copyright (c) 2026 Scott Armstrong and Amélie Loher. All rights reserved.
-- Released under Apache 2.0 license as described in the file LICENSE.
module

public import RothschildStein.H2.Truncation
public import Mathlib.MeasureTheory.Measure.WithDensity

@[expose] public section

set_option autoImplicit false
set_option relaxedAutoImplicit false

noncomputable section

open Set MeasureTheory
open scoped ENNReal NNReal

namespace RothschildStein.H2

variable {Y : Type*} [MeasurableSpace Y]

/-- A positive power moment is unchanged on restricting the measure to
any set supporting the function (BB Thm 7.48, p. 334; Tonelli theorem). -/
theorem moment_restrict_support (ν : Measure Y) {f : Y → ℝ} {s : Set Y}
    (hs : ∀ y ∉ s, f y = 0) {p : ℝ} (hp : 0 < p) :
    moment (ν.restrict s) p f = moment ν p f := by
  apply setLIntegral_eq_of_support_subset
  intro y hy
  by_contra h
  have hz := hs y h
  exact hy (by simp [hz, Real.zero_rpow hp.ne'])

/-- Finite positive moments make the input measure s-finite on the
nonzero support. This discharges Tonelli's measure assumption without a global
sigma-finiteness hypothesis on the input (BB Thm 7.48, p. 334). -/
theorem sFinite_restrict_of_moment_lt_top (ν : Measure Y) {f : Y → ℝ}
    (hf : Measurable f) {p : ℝ} (hp : 0 < p) (hfin : moment ν p f < ∞) :
    SFinite (ν.restrict {y | f y ≠ 0}) := by
  let μ := ν.restrict {y | f y ≠ 0}
  let d : Y → ℝ≥0∞ := fun y => ENNReal.ofReal (|f y| ^ p)
  have hd : Measurable d := by
    simpa only [d, Real.norm_eq_abs] using (hf.norm.pow_const p).ennreal_ofReal
  have hμfin : ∫⁻ y, d y ∂μ < ∞ := by
    change moment μ p f < ∞
    rw [moment_restrict_support ν (by simp) hp]
    exact hfin
  let : IsFiniteMeasure (μ.withDensity d) := isFiniteMeasure_withDensity hμfin.ne
  have hdpos : ∀ᵐ y ∂μ, d y ≠ 0 := by
    filter_upwards [ae_restrict_mem ((measurableSet_eq_fun hf measurable_const).compl)] with y hy
    have hfy : 0 < |f y| := abs_pos.mpr hy
    exact (ENNReal.ofReal_pos.mpr (Real.rpow_pos_of_pos hfy p)).ne'
  exact sFinite_of_absolutelyContinuous (withDensity_absolutelyContinuous' hd.aemeasurable hdpos)

end RothschildStein.H2

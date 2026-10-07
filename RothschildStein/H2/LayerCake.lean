-- Copyright (c) 2026 Scott Armstrong and Amélie Loher. All rights reserved.
-- Released under Apache 2.0 license as described in the file LICENSE.
module

public import Mathlib.Analysis.SpecialFunctions.Pow.Integral
public import Mathlib.MeasureTheory.Function.LpSeminorm.ChebyshevMarkov

@[expose] public section

set_option autoImplicit false
set_option relaxedAutoImplicit false

noncomputable section

open Set MeasureTheory
open scoped ENNReal NNReal

namespace RothschildStein.H2

variable {Y : Type*} [MeasurableSpace Y]

/-- The power moment used in diagonal interpolation (BB Lemma 7.26, p. 314). -/
def moment (ν : Measure Y) (p : ℝ) (f : Y → ℝ) : ℝ≥0∞ :=
  ∫⁻ y, ENNReal.ofReal (|f y| ^ p) ∂ν

/-- Distribution of a real function (BB Lemma 7.26, p. 314). -/
def distribution (ν : Measure Y) (f : Y → ℝ) (t : ℝ) : ℝ≥0∞ :=
  ν {y | t < |f y|}

/-- Layer cake with strict superlevel sets, without a finiteness
assumption on the measure (BB Lemma 7.26, p. 314). -/
theorem layerCake (ν : Measure Y) {f : Y → ℝ} (hf : AEMeasurable f ν)
    {p : ℝ} (hp : 0 < p) :
    moment ν p f = ENNReal.ofReal p *
      ∫⁻ t in Ioi (0 : ℝ), distribution ν f t * ENNReal.ofReal (t ^ (p - 1)) := by
  exact lintegral_rpow_eq_lintegral_meas_lt_mul ν
    (ae_of_all _ fun y => abs_nonneg (f y)) (by simpa only [Real.norm_eq_abs] using hf.norm) hp

/-- Chebyshev in the ENNReal formulation, including infinite values
(BB Lemma 7.26, p. 314). -/
theorem chebyshev_ennreal (ν : Measure Y) {F : Y → ℝ≥0∞}
    (hF : AEMeasurable F ν) (s : ℝ≥0∞) :
    s * ν {y | s ≤ F y} ≤ ∫⁻ y, F y ∂ν := by
  exact mul_meas_ge_le_lintegral₀ hF s

end RothschildStein.H2

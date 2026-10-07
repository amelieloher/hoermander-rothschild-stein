-- Copyright (c) 2026 Scott Armstrong and Amélie Loher. All rights reserved.
-- Released under Apache 2.0 license as described in the file LICENSE.
module

public import RothschildStein.H3.DilationLp
public import Mathlib.MeasureTheory.Function.LpSeminorm.Indicator
public import Mathlib.Tactic.Linarith

set_option autoImplicit false
set_option relaxedAutoImplicit false
@[expose] public section
noncomputable section
namespace RothschildStein.H3
open MeasureTheory Set
open scoped ENNReal
variable {N : ℕ} (G : HomogeneousGroup N)

/-- Exact Lp dilation on an origin gauge ball, including infinite norms. -/
theorem eLpNorm_dilate_gauge_sublevel {ν : (Fin N → ℝ) → ℝ}
    (hν : G.IsHomogeneousGauge ν) (f : (Fin N → ℝ) → ℝ) (p : ℝ≥0∞)
    (R : ℝ) {t : ℝ} (ht : 0 < t) :
    eLpNorm (fun x => f (G.dilate t x)) p (volume.restrict {x | ν x < R}) =
      ENNReal.ofReal ((t ^ G.homogeneousDimension)⁻¹) ^ (1 / p.toReal) *
        eLpNorm f p (volume.restrict {x | ν x < t * R}) := by
  have hA : MeasurableSet {x | ν x < R} :=
    (isOpen_lt hν.1 continuous_const).measurableSet
  have hB : MeasurableSet {x | ν x < t * R} :=
    (isOpen_lt hν.1 continuous_const).measurableSet
  have he : (fun x => ({y | ν y < t * R}.indicator f) (G.dilate t x)) =
      {x | ν x < R}.indicator (fun x => f (G.dilate t x)) := by
    funext x
    have hm : G.dilate t x ∈ {y | ν y < t * R} ↔ x ∈ {y | ν y < R} := by
      change ν (G.dilate t x) < t * R ↔ ν x < R
      rw [hν.2.2.2 t ht]
      constructor <;> intro h <;> nlinarith
    by_cases hx : x ∈ {y | ν y < R}
    · rw [indicator_of_mem (hm.mpr hx), indicator_of_mem hx]
    · rw [indicator_of_notMem (fun h => hx (hm.mp h)), indicator_of_notMem hx]
  rw [← eLpNorm_indicator_eq_eLpNorm_restrict hA, ← he,
    eLpNorm_dilate G _ p ht, eLpNorm_indicator_eq_eLpNorm_restrict hB]

end RothschildStein.H3

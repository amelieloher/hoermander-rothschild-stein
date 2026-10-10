-- Copyright (c) 2026 Scott Armstrong and Amélie Loher. All rights reserved.
-- Released under Apache 2.0 license as described in the file LICENSE.
module

public import Mathlib.MeasureTheory.Function.LpSpace.ContinuousCompMeasurePreserving
public import Mathlib.MeasureTheory.Function.LpSpace.Complete
public import Mathlib.MeasureTheory.Measure.Lebesgue.Basic
public import Mathlib.MeasureTheory.Integral.IntervalIntegral.FundThmCalculus
public import Mathlib.MeasureTheory.Integral.Bochner.ContinuousLinearMap

/-!
# Time translations and Steklov averages in L²

Time translation acts continuously and isometrically on Bochner L². Integrating this
continuous orbit gives forward and backward time averages that converge strongly in L².
-/

@[expose] public section

noncomputable section

open Set MeasureTheory Filter
open scoped Topology

namespace HeatKernel

variable {E : Type*} [NormedAddCommGroup E]

/-- Translation of a Bochner L² class in the time variable. -/
def timeTranslate (s : ℝ) (u : Lp E 2 (volume : Measure ℝ)) : Lp E 2 (volume : Measure ℝ) :=
  Lp.compMeasurePreserving (fun t : ℝ => t + s) (measurePreserving_add_right volume s) u

/-- The translated class has the expected almost-everywhere representative. -/
theorem timeTranslate_ae_eq (s : ℝ) (u : Lp E 2 (volume : Measure ℝ)) :
    timeTranslate s u =ᵐ[volume] fun t => u (t + s) :=
  Lp.coeFn_compMeasurePreserving _ _

@[simp]
theorem timeTranslate_zero (u : Lp E 2 (volume : Measure ℝ)) : timeTranslate 0 u = u := by
  apply Lp.ext
  filter_upwards [timeTranslate_ae_eq 0 u] with t ht
  simpa using ht

/-- The orbit of every Bochner L² function under time translation is continuous. -/
theorem continuous_timeTranslate (u : Lp E 2 (volume : Measure ℝ)) :
    Continuous (fun s => timeTranslate s u) := by
  let T : ℝ → C(ℝ, ℝ) := fun s => ⟨fun t => t + s, continuous_id.add continuous_const⟩
  have hT : Continuous T := ContinuousMap.continuous_of_continuous_uncurry T
    (continuous_snd.add continuous_fst)
  exact continuous_const.compMeasurePreservingLp hT
    (fun s => measurePreserving_add_right volume s) (by norm_num)

variable [NormedSpace ℝ E] [CompleteSpace E]

/-- The forward average of time translations, as a Bochner L² class. -/
def steklovForward (h : ℝ) (u : Lp E 2 (volume : Measure ℝ)) : Lp E 2 (volume : Measure ℝ) :=
  h⁻¹ • ∫ s in (0 : ℝ)..h, timeTranslate s u

/-- The backward average of time translations, as a Bochner L² class. -/
def steklovBackward (h : ℝ) (u : Lp E 2 (volume : Measure ℝ)) : Lp E 2 (volume : Measure ℝ) :=
  h⁻¹ • ∫ s in (0 : ℝ)..h, timeTranslate (-s) u

/-- Averages of a continuous Banach-valued curve converge to its value at zero. -/
theorem tendsto_intervalAverage {f : ℝ → E} (hf : Continuous f) :
    Tendsto (fun h : ℝ => h⁻¹ • ∫ s in (0 : ℝ)..h, f s) (𝓝[>] 0) (𝓝 (f 0)) := by
  have hd := intervalIntegral.integral_hasDerivAt_right (hf.intervalIntegrable 0 0)
    (hf.stronglyMeasurableAtFilter volume (𝓝 0)) hf.continuousAt
  simpa using hd.tendsto_slope_zero_right

/-- Forward Steklov averages converge strongly in Bochner L². -/
theorem tendsto_steklovForward (u : Lp E 2 (volume : Measure ℝ)) :
    Tendsto (fun h => steklovForward h u) (𝓝[>] 0) (𝓝 u) := by
  simpa [steklovForward] using tendsto_intervalAverage (continuous_timeTranslate u)

end HeatKernel

-- Copyright (c) 2026 Scott Armstrong and Amélie Loher. All rights reserved.
-- Released under Apache 2.0 license as described in the file LICENSE.
module

public import HeatKernel.Form.TimeAverages
public import HeatKernel.Form.IntegralRepresentatives

/-!
# Pointwise representatives of Steklov averages

The L² averages are represented by the usual forward and backward Bochner integrals on time
intervals. Consequently these literal time averages converge strongly in Bochner L².
-/

@[expose] public section

noncomputable section

open Set MeasureTheory Filter
open scoped Topology ENNReal

namespace HeatKernel

section AverageFunctions

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]

/-- The forward Bochner time average of a function. -/
def forwardTimeAverage (h : ℝ) (u : ℝ → E) (t : ℝ) : E :=
  h⁻¹ • ∫ s in t..t + h, u s

/-- The backward Bochner time average of a function. -/
def backwardTimeAverage (h : ℝ) (u : ℝ → E) (t : ℝ) : E :=
  h⁻¹ • ∫ s in t - h..t, u s

/-- Almost-everywhere changes of a function leave each forward time average unchanged. -/
theorem forwardTimeAverage_congr_ae {u v : ℝ → E} (huv : u =ᵐ[volume] v) (h : ℝ) :
    forwardTimeAverage h u = forwardTimeAverage h v := by
  funext t
  unfold forwardTimeAverage
  congr 1
  apply intervalIntegral.integral_congr_ae
  filter_upwards [huv] with s hs
  exact fun _ => hs

/-- Almost-everywhere changes of a function leave each backward time average unchanged. -/
theorem backwardTimeAverage_congr_ae {u v : ℝ → E} (huv : u =ᵐ[volume] v) (h : ℝ) :
    backwardTimeAverage h u = backwardTimeAverage h v := by
  funext t
  unfold backwardTimeAverage
  congr 1
  apply intervalIntegral.integral_congr_ae
  filter_upwards [huv] with s hs
  exact fun _ => hs

end AverageFunctions

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [CompleteSpace E]

/-- The forward L² average has the usual pointwise integral representative. -/
theorem steklovForward_ae_eq {h : ℝ} (hh : 0 ≤ h) (u : Lp E 2 (volume : Measure ℝ)) :
    steklovForward h u =ᵐ[volume] forwardTimeAverage h u := by
  have hint : IntegrableOn (fun s => timeTranslate s u) (Ioc 0 h) volume :=
    (intervalIntegrable_iff_integrableOn_Ioc_of_le hh).mp
      ((continuous_timeTranslate u).intervalIntegrable _ _)
  have hrep := integral_L2_ae_eq_integral (f := fun s t => u (t + s)) hint
    (by simpa only [Function.uncurry_def, Function.comp_def, Pi.add_apply, Pi.sub_apply] using
      (Lp.stronglyMeasurable u).comp_measurable (measurable_snd.add measurable_fst))
    (Eventually.of_forall fun s => timeTranslate_ae_eq s u)
  rw [← intervalIntegral.integral_of_le hh] at hrep
  filter_upwards [Lp.coeFn_smul h⁻¹ (∫ s in (0 : ℝ)..h, timeTranslate s u), hrep] with t ht hrt
  rw [show (steklovForward h u) t = h⁻¹ • (∫ s in (0 : ℝ)..h, timeTranslate s u) t from ht,
    hrt]
  rw [← intervalIntegral.integral_of_le hh]
  simp only [forwardTimeAverage, intervalIntegral.integral_comp_add_left, add_zero]

/-- The backward L² average has the usual pointwise integral representative. -/
theorem steklovBackward_ae_eq {h : ℝ} (hh : 0 ≤ h) (u : Lp E 2 (volume : Measure ℝ)) :
    steklovBackward h u =ᵐ[volume] backwardTimeAverage h u := by
  have hc : Continuous (fun s => timeTranslate (-s) u) :=
    (continuous_timeTranslate u).comp continuous_neg
  have hint : IntegrableOn (fun s => timeTranslate (-s) u) (Ioc 0 h) volume :=
    (intervalIntegrable_iff_integrableOn_Ioc_of_le hh).mp (hc.intervalIntegrable _ _)
  have hrep := integral_L2_ae_eq_integral (f := fun s t => u (t - s)) hint
    (by simpa only [Function.uncurry_def, Function.comp_def, Pi.add_apply, Pi.sub_apply] using
      (Lp.stronglyMeasurable u).comp_measurable (measurable_snd.sub measurable_fst))
    (Eventually.of_forall fun s => by simpa only [sub_eq_add_neg] using timeTranslate_ae_eq (-s) u)
  rw [← intervalIntegral.integral_of_le hh] at hrep
  filter_upwards [Lp.coeFn_smul h⁻¹ (∫ s in (0 : ℝ)..h, timeTranslate (-s) u), hrep] with t ht hrt
  rw [show (steklovBackward h u) t = h⁻¹ • (∫ s in (0 : ℝ)..h, timeTranslate (-s) u) t from ht,
    hrt]
  rw [← intervalIntegral.integral_of_le hh]
  simp only [backwardTimeAverage, intervalIntegral.integral_comp_sub_left, sub_zero]

/-- Forward pointwise averages converge in the global Bochner L² seminorm. -/
theorem tendsto_eLpNorm_forwardTimeAverage_sub (u : Lp E 2 (volume : Measure ℝ)) :
    Tendsto (fun h => eLpNorm (forwardTimeAverage h u - ⇑u) 2 volume)
      (𝓝[>] 0) (𝓝 0) := by
  have hlim := (tendsto_steklovForward u).edist (tendsto_const_nhds (x := u))
  simp only [edist_self] at hlim
  apply hlim.congr'
  filter_upwards [self_mem_nhdsWithin] with h hh
  rw [Lp.edist_def]
  exact eLpNorm_congr_ae ((steklovForward_ae_eq hh.le u).sub ae_eq_rfl)

/-- Forward time averages of an arbitrary Bochner L² function converge in L². -/
theorem tendsto_eLpNorm_forwardTimeAverage_sub_of_memLp {u : ℝ → E}
    (hu : MemLp u 2 volume) :
    Tendsto (fun h => eLpNorm (forwardTimeAverage h u - u) 2 volume)
      (𝓝[>] 0) (𝓝 0) := by
  apply (tendsto_eLpNorm_forwardTimeAverage_sub (hu.toLp u)).congr
  intro h
  apply eLpNorm_congr_ae
  exact (EventuallyEq.of_eq (forwardTimeAverage_congr_ae hu.coeFn_toLp h)).sub hu.coeFn_toLp

end HeatKernel

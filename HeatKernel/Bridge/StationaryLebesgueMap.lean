-- Copyright (c) 2026 Scott Armstrong and Amélie Loher. All rights reserved.
-- Released under Apache 2.0 license as described in the file LICENSE.
module

public import HeatKernel.Bridge.StationaryLebesgueNorm
import Mathlib.Tactic

/-! # Continuous linear extension of spatial L² functions as stationary functions -/

@[expose] public section
noncomputable section
open Set MeasureTheory
open scoped ENNReal
namespace HeatKernel

variable {α β : Type*} [MeasurableSpace α] [MeasurableSpace β]
    (μ : Measure α) (ν : Measure β) [IsFiniteMeasure μ] [SFinite ν]

/-- A spatial L² element, held constant in time as a product L² element. -/
def stationaryLp (v : Lp ℝ 2 ν) : Lp ℝ 2 (μ.prod ν) :=
  ((Lp.memLp v).comp_snd μ).toLp (fun z : α × β => v z.2)

/-- The stationary representative is the spatial representative on almost every pair. -/
theorem stationaryLp_coeFn (v : Lp ℝ 2 ν) :
    (stationaryLp μ ν v : α × β → ℝ) =ᵐ[μ.prod ν] fun z => v z.2 :=
  ((Lp.memLp v).comp_snd μ).coeFn_toLp

/-- Stationary extension respects addition. -/
theorem stationaryLp_add (v w : Lp ℝ 2 ν) :
    stationaryLp μ ν (v + w) = stationaryLp μ ν v + stationaryLp μ ν w := by
  apply Lp.ext
  have h := Measure.quasiMeasurePreserving_snd (μ := μ) (ν := ν) |>.ae_eq_comp (Lp.coeFn_add v w)
  filter_upwards [stationaryLp_coeFn μ ν (v + w), stationaryLp_coeFn μ ν v,
    stationaryLp_coeFn μ ν w, Lp.coeFn_add (stationaryLp μ ν v) (stationaryLp μ ν w), h]
    with z hsum hv hw hadd hz
  simp only [Function.comp_def, Pi.add_apply] at hz hadd
  exact hsum.trans (hz.trans ((congrArg₂ (· + ·) hv.symm hw.symm).trans hadd.symm))

/-- Stationary extension respects real scalar multiplication. -/
theorem stationaryLp_smul (c : ℝ) (v : Lp ℝ 2 ν) :
    stationaryLp μ ν (c • v) = c • stationaryLp μ ν v := by
  apply Lp.ext
  have h := Measure.quasiMeasurePreserving_snd (μ := μ) (ν := ν) |>.ae_eq_comp (Lp.coeFn_smul c v)
  filter_upwards [stationaryLp_coeFn μ ν (c • v), stationaryLp_coeFn μ ν v,
    Lp.coeFn_smul c (stationaryLp μ ν v), h] with z hcv hv hsmul hz
  simp only [Function.comp_def, Pi.smul_apply] at hz hsmul
  exact hcv.trans (hz.trans ((congrArg (c • ·) hv.symm).trans hsmul.symm))

/-- Stationary extension is linear. -/
def stationaryLpLinearMap : Lp ℝ 2 ν →ₗ[ℝ] Lp ℝ 2 (μ.prod ν) where
  toFun := stationaryLp μ ν
  map_add' := stationaryLp_add μ ν
  map_smul' := stationaryLp_smul μ ν

/-- Stationary extension has the exact finite-time norm scaling. -/
theorem norm_stationaryLp (v : Lp ℝ 2 ν) :
    ‖stationaryLp μ ν v‖ = ((μ univ) ^ (1 / 2 : ℝ)).toReal * ‖v‖ := by
  rw [stationaryLp, norm_toLp_two_comp_snd μ (Lp.memLp v)]
  rw [Lp.toLp_coeFn v (Lp.memLp v)]

/-- Stationary extension is a continuous linear map on L². -/
def stationaryLpContinuousLinearMap : Lp ℝ 2 ν →L[ℝ] Lp ℝ 2 (μ.prod ν) :=
  (stationaryLpLinearMap μ ν).mkContinuous ((μ univ) ^ (1 / 2 : ℝ)).toReal
    (fun v => (norm_stationaryLp μ ν v).le)

end HeatKernel

-- Copyright (c) 2026 Scott Armstrong and Amélie Loher. All rights reserved.
-- Released under Apache 2.0 license as described in the file LICENSE.
module

public import HeatKernel.Form.GraphForm
public import HeatKernel.Bridge.DualPrecomposition
public import Mathlib.MeasureTheory.Function.L2Space
import Mathlib.Tactic.Linter
import all Mathlib.Basic.Real.Basic
import all Mathlib.Basic.Real.Star

/-! # Spatial L² values as continuous form-domain functionals -/

@[expose] public section
noncomputable section
open Set MeasureTheory TopologicalSpace
namespace HeatKernel

variable {N q : ℕ} (U : Opens (Fin N → ℝ))
    (X : Fin q → (Fin N → ℝ) → (Fin N → ℝ))

/-- A spatial square-integrable value defines a bounded functional on the form domain. -/
def spatialValueFunctional : SpatialL2 U →L[ℝ] (energyGraph U X →L[ℝ] ℝ) := by
  let B : SpatialL2 U →L[ℝ] (SpatialL2 U →L[ℝ] ℝ) := innerSL ℝ
  exact (dualPrecomposition (energyInclusion U X)).comp B

/-- Evaluation is the concrete spatial value pairing. -/
theorem spatialValueFunctional_apply (f : SpatialL2 U) (v : energyGraph U X) :
    spatialValueFunctional U X f v =
      ∫ x, f x * (v : GradientSpace U q).fst x ∂volume.restrict (U : Set (Fin N → ℝ)) := by
  change inner ℝ f (energyInclusion U X v) = _
  rw [L2.inner_def]
  simp only [Real.inner_apply, energyInclusion_apply]

/-- The spatial L² norm controls evaluation on the form-domain value coordinate. -/
theorem norm_spatialValueFunctional_apply_le (f : SpatialL2 U) (v : energyGraph U X) :
    ‖spatialValueFunctional U X f v‖ ≤ ‖f‖ * ‖energyInclusion U X v‖ := by
  change ‖inner ℝ f (energyInclusion U X v)‖ ≤ _
  exact norm_inner_le_norm (𝕜 := ℝ) f (energyInclusion U X v)

/-- A Bochner L² spatial value gives a Bochner L² curve in the form-domain dual. -/
theorem memLp_spatialValueFunctional {α : Type*} [MeasurableSpace α]
    {μ : Measure α} {f : α → SpatialL2 U} (hf : MemLp f 2 μ) :
    MemLp (fun t => spatialValueFunctional U X (f t)) 2 μ := by
  let B : SpatialL2 U →L[ℝ] (SpatialL2 U →L[ℝ] ℝ) := innerSL ℝ
  have hB : MemLp (fun t => B (f t)) 2 μ := hf.continuousLinearMap_comp (𝕜 := ℝ) B
  exact memLp_dualPrecomposition (energyInclusion U X) hB

end HeatKernel

-- Copyright (c) 2026 Scott Armstrong and Amélie Loher. All rights reserved.
-- Released under Apache 2.0 license as described in the file LICENSE.
module

public import HeatKernel.Form.GraphForm
public import Mathlib.MeasureTheory.Function.L2Space
public import HeatKernel.Bridge.DualPrecomposition
import Mathlib.Tactic.Linter
import all Mathlib.Analysis.Normed.Operator.Basic
import all Mathlib.Basic.Real.Basic
import all Mathlib.Basic.Real.Star

/-! # Horizontal fluxes as continuous form-domain functionals -/

@[expose] public section
noncomputable section
open Set MeasureTheory TopologicalSpace
namespace HeatKernel

variable {N q : ℕ} (U : Opens (Fin N → ℝ))
    (X : Fin q → (Fin N → ℝ) → (Fin N → ℝ))

/-- A square-integrable horizontal flux defines a continuous linear form test. -/
def horizontalFluxFunctional :
    PiLp 2 (fun _ : Fin q => SpatialL2 U) →L[ℝ] (energyGraph U X →L[ℝ] ℝ) :=
  by
    let B : PiLp 2 (fun _ : Fin q => SpatialL2 U) →L[ℝ]
        (PiLp 2 (fun _ : Fin q => SpatialL2 U) →L[ℝ] ℝ) := innerSL ℝ
    exact (dualPrecomposition (energyGradient U X)).comp B

/-- Evaluation is the sum of the concrete flux-gradient integrals. -/
theorem horizontalFluxFunctional_apply
    (F : PiLp 2 (fun _ : Fin q => SpatialL2 U)) (v : energyGraph U X) :
    horizontalFluxFunctional U X F v =
      ∑ i, ∫ x, F i x * (v : GradientSpace U q).snd i x
        ∂volume.restrict (U : Set (Fin N → ℝ)) := by
  change inner ℝ F (energyGradient U X v) = _
  rw [PiLp.inner_apply]
  apply Finset.sum_congr rfl
  intro i _
  rw [L2.inner_def]
  simp only [Real.inner_apply, energyGradient_apply]

/-- A Bochner L² flux gives a Bochner L² curve in the form-domain dual. -/
theorem memLp_horizontalFluxFunctional {α : Type*} [MeasurableSpace α]
    {μ : Measure α} {F : α → PiLp 2 (fun _ : Fin q => SpatialL2 U)}
    (hF : MemLp F 2 μ) : MemLp (fun t => horizontalFluxFunctional U X (F t)) 2 μ :=
  by
    let B : PiLp 2 (fun _ : Fin q => SpatialL2 U) →L[ℝ]
        (PiLp 2 (fun _ : Fin q => SpatialL2 U) →L[ℝ] ℝ) := innerSL ℝ
    have hB : MemLp (fun t => B (F t)) 2 μ := hF.continuousLinearMap_comp (𝕜 := ℝ) B
    exact memLp_dualPrecomposition (energyGradient U X) hB

end HeatKernel

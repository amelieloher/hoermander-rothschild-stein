-- Copyright (c) 2026 Scott Armstrong and Amélie Loher. All rights reserved.
-- Released under Apache 2.0 license as described in the file LICENSE.
module

public import HeatKernel.Moser.WeakSolutionAffineEnergyIdentity
public import HeatKernel.Moser.LogarithmicReciprocalTest
public import HeatKernel.Form.PositivePartApproximation
public import Mathlib.Analysis.Calculus.ContDiff.RCLike
public import Mathlib.MeasureTheory.Integral.Prod
public import Mathlib.MeasureTheory.Integral.DominatedConvergence
public import HeatKernel.Moser.WeakSolutionTimeTesting
public import HeatKernel.Moser.WeakSolutionSpatialTransport
public import HeatKernel.Moser.WeakSolutionEnergyInterface
public import HeatKernel.Moser.WeakSolutionCutoffDualEquation
public import HeatKernel.Moser.WeakSolutionSpatialEnergyIdentity
public import HeatKernel.Bridge.ParabolicCoefficientBounds
public import HeatKernel.Form.ParabolicEnergyCurves
public import HeatKernel.Moser.JointMeasurability

import all Mathlib.Basic.Real.Basic
import all Mathlib.Analysis.Normed.Operator.Basic
import all Mathlib.Analysis.Normed.Operator.NormedSpace
import all Mathlib.Topology.Algebra.Module.Spaces.ContinuousLinearMap

/-! # Positive-part subsolution tests supplied by local weak solutions

The local value and horizontal-gradient bounds supply the spacetime L² inputs
for the corner limit. The spatial weight has compact support and locally L²
horizontal derivatives. The gradient representative is chosen once for every
compact temporal interval and every temporal test.
-/

@[expose] public section
set_option autoImplicit false
set_option relaxedAutoImplicit false
noncomputable section
open Set MeasureTheory Filter TopologicalSpace RothschildStein
namespace HeatKernel

/-- Local essential L∞ time bounds on spatial L² norms give spacetime L²
membership of the value on compact cylinders. -/
theorem WeakSolutionEnergyInterface.memLp_value_on_compact_cylinder
    {N q : ℕ} {X : Fin q → (Fin N → ℝ) → (Fin N → ℝ)}
    {coeff : ℝ → (Fin N → ℝ) → Fin q → Fin q → ℝ}
    {I : Opens ℝ} {U : Opens (Fin N → ℝ)}
    {u : ℝ → (Fin N → ℝ) → ℝ} {g : Fin q → ℝ → (Fin N → ℝ) → ℝ}
    (hg : WeakSolutionEnergyInterface X coeff I U u g)
    (hum : AEStronglyMeasurable (Function.uncurry u)
      (volume.restrict ((I : Set ℝ) ×ˢ (U : Set (Fin N → ℝ)))))
    {J : Set ℝ} {K : Set (Fin N → ℝ)}
    (hJ : IsCompact J) (hJI : J ⊆ (I : Set ℝ))
    (hK : IsCompact K) (hKU : K ⊆ (U : Set (Fin N → ℝ))) :
    MemLp (Function.uncurry u) 2 ((volume.restrict J).prod (volume.restrict K)) := by
  let : IsFiniteMeasure (volume.restrict J) := ⟨by
    rw [Measure.restrict_apply_univ]
    exact hJ.measure_lt_top⟩
  have hmeas : AEStronglyMeasurable (Function.uncurry u)
      ((volume.restrict J).prod (volume.restrict K)) := by
    rw [Measure.prod_restrict, ← Measure.volume_eq_prod]
    exact hum.mono_measure (Measure.restrict_mono (prod_mono hJI hKU) le_rfl)
  exact memLp_product_of_essSup_spatial_eLpNorm_lt_top hmeas
    (hg.local_bounds J K hJ hJI hK hKU).1

end HeatKernel

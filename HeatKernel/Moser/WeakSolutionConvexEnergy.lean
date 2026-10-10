-- Copyright (c) 2026 Scott Armstrong and Amélie Loher. All rights reserved.
-- Released under Apache 2.0 license as described in the file LICENSE.
module

public import HeatKernel.Moser.WeakSolutionSpatialEnergyIdentity
public import HeatKernel.Form.TimeDependentEnergyPairings
public import Mathlib.Analysis.Convex.Deriv
public import Mathlib.Analysis.Calculus.Deriv.Slope

import all Mathlib.Basic.Real.Basic
import all Mathlib.Analysis.Normed.Operator.Basic
import all Mathlib.Analysis.Normed.Operator.NormedSpace
import all Mathlib.Topology.Algebra.Module.Spaces.ContinuousLinearMap

/-! # Nonnegative principal energies for convex compositions

The principal term is evaluated on the original energy curve. Convexity is used
after the averaged flux-pairing identity has passed to its limit.
-/

@[expose] public section
set_option autoImplicit false
set_option relaxedAutoImplicit false
noncomputable section
open Set MeasureTheory TopologicalSpace Filter
open scoped NNReal
namespace HeatKernel

/-- The unweighted nonlinear test of an L² zero-boundary curve is again an L² curve. -/
theorem WeakSolutionScalarTest.memLp_energyMap (T : WeakSolutionScalarTest) {N q : ℕ}
    (V : Opens (Fin N → ℝ)) (X : Fin q → (Fin N → ℝ) → (Fin N → ℝ))
    (hX : ∀ i, ContDiff ℝ (⊤ : ℕ∞) (X i)) {μ : Measure ℝ}
    {v : ℝ → zeroBoundaryGraph V X} (hv : MemLp v 2 μ) :
    MemLp (fun t => T.energyMap V X hX (v t)) 2 μ := by
  apply (hv.const_smul (T.bound : ℝ)).of_le
    ((T.continuous_energyMap V X hX).comp_aestronglyMeasurable hv.aestronglyMeasurable)
  exact Eventually.of_forall fun t => by
    simpa only [Pi.smul_apply, norm_smul, Real.norm_of_nonneg T.bound.coe_nonneg] using
      T.norm_energyMap_le V X hX (v t)

end HeatKernel

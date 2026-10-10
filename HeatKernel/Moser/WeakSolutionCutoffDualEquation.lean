-- Copyright (c) 2026 Scott Armstrong and Amélie Loher. All rights reserved.
-- Released under Apache 2.0 license as described in the file LICENSE.
module

public import HeatKernel.Moser.WeakSolutionLocalDualEquation
public import HeatKernel.Moser.WeakSolutionEnergyTesting
public import HeatKernel.Moser.TimeAverageFunctionals
public import HeatKernel.Bridge.WeakCutoffValueEndpoints

import all Mathlib.Basic.Real.Basic
import all Mathlib.Analysis.Normed.Operator.Basic
import all Mathlib.Analysis.Normed.Operator.NormedSpace
import all Mathlib.Topology.Algebra.Module.Spaces.ContinuousLinearMap

/-! # Regularized time equations for cutoff energy curves -/

@[expose] public section
set_option autoImplicit false
set_option relaxedAutoImplicit false
noncomputable section
open Set MeasureTheory TopologicalSpace
open scoped NNReal ENNReal
namespace HeatKernel

/-- The weak cutoff pair supplies its regularized dual time equation directly.
No time differentiability or averaged dual identity is assumed. -/
theorem IsZeroBoundaryWeakCutoffEnergyTimePair.ae_regularized_dual_time_equation
    {N q : ℕ} {V : Opens (Fin N → ℝ)}
    {X : Fin q → (Fin N → ℝ) → (Fin N → ℝ)}
    {coeff : ℝ → (Fin N → ℝ) → Fin q → Fin q → ℝ}
    {u : ℝ → (Fin N → ℝ) → ℝ} {g : Fin q → ℝ → (Fin N → ℝ) → ℝ}
    {φ : (Fin N → ℝ) → ℝ} {k : Fin q → (Fin N → ℝ) → ℝ}
    {v : ℝ → zeroBoundaryGraph V X} {F : ℝ → (zeroBoundaryGraph V X →L[ℝ] ℝ)}
    {a b h : ℝ} (hp : IsZeroBoundaryWeakCutoffEnergyTimePair V X coeff (Icc a b) u g φ k v F)
    (hh : 0 ≤ h) :
    ∀ᵐ t ∂volume, t ∈ Ioo a (b - h) →
      zeroBoundaryValueFunctional V X (h⁻¹ • (v (t + h) - v t)) =
        -forwardTimeAverage h F t := by
  let : InnerProductSpace ℝ (zeroBoundaryGraph V X) :=
    {(inferInstance : InnerProductSpace ℝ (zeroBoundaryGraph V X)) with
      toNormedSpace := (inferInstance : NormedSpace ℝ (zeroBoundaryGraph V X))}
  have he := SatisfiesDualTimeBalance.ae_forward_difference_eq_of_memLp_restrict
    (E := zeroBoundaryGraph V X) hp.2.2.2.2.2.2
    (memLp_zeroBoundaryValueFunctional V X hp.1) hp.2.2.2.2.1 hh
  filter_upwards [he] with t ht
  intro hm
  simpa only [map_smul, map_sub] using ht hm

end HeatKernel

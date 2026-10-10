-- Copyright (c) 2026 Scott Armstrong and Amélie Loher. All rights reserved.
-- Released under Apache 2.0 license as described in the file LICENSE.
module

public import HeatKernel.Bridge.SpatialValueFunctional
public import HeatKernel.Bridge.ZeroBoundaryDualRestriction
import Mathlib.Tactic.Linter
import all Mathlib.Basic.Real.Basic
import all Mathlib.Analysis.Normed.Operator.Basic

/-! # Spatial value pairings on zero-boundary form domains -/

@[expose] public section
noncomputable section
open Set MeasureTheory TopologicalSpace
namespace HeatKernel

variable {N q : ℕ} (V : Opens (Fin N → ℝ))
    (X : Fin q → (Fin N → ℝ) → (Fin N → ℝ))

/-- A zero-boundary form value acts on the same form domain by its spatial L² pairing. -/
def zeroBoundaryValueFunctional :
    zeroBoundaryGraph V X →L[ℝ] (zeroBoundaryGraph V X →L[ℝ] ℝ) := by
  let A : zeroBoundaryGraph V X →L[ℝ] energyGraph (N := N) ⊤ X :=
    zeroBoundaryEnergyInclusion V X
  let B : zeroBoundaryGraph V X →L[ℝ] SpatialL2 (N := N) ⊤ :=
    (energyInclusion ⊤ X).comp A
  let C : SpatialL2 (N := N) ⊤ →L[ℝ] (zeroBoundaryGraph V X →L[ℝ] ℝ) :=
    (zeroBoundaryDualRestriction V X).comp (spatialValueFunctional ⊤ X)
  exact C.comp B

/-- Evaluation is the literal global spatial value pairing. -/
theorem zeroBoundaryValueFunctional_apply (v w : zeroBoundaryGraph V X) :
    zeroBoundaryValueFunctional V X v w =
      ∫ x, (v : GradientSpace (N := N) ⊤ q).fst x *
        (w : GradientSpace (N := N) ⊤ q).fst x := by
  change spatialValueFunctional ⊤ X (v : GradientSpace (N := N) ⊤ q).fst
    (zeroBoundaryEnergyInclusion V X w) = _
  rw [spatialValueFunctional_apply]
  simp only [Opens.coe_top, Measure.restrict_univ]
  rfl

/-- Zero-boundary L² energy curves give L² value curves in the same form dual. -/
theorem memLp_zeroBoundaryValueFunctional {T : Type*} [MeasurableSpace T]
    {μ : Measure T} {v : T → zeroBoundaryGraph V X} (hv : MemLp v 2 μ) :
    MemLp (fun t => zeroBoundaryValueFunctional V X (v t)) 2 μ :=
  by
    have hA : MemLp (fun t => zeroBoundaryEnergyInclusion V X (v t)) 2 μ :=
      hv.continuousLinearMap_comp (𝕜 := ℝ) (zeroBoundaryEnergyInclusion V X)
    have hB : MemLp (fun t => energyInclusion ⊤ X (zeroBoundaryEnergyInclusion V X (v t))) 2 μ :=
      hA.continuousLinearMap_comp (𝕜 := ℝ) (energyInclusion ⊤ X)
    exact memLp_zeroBoundaryDualRestriction V X (memLp_spatialValueFunctional ⊤ X hB)

end HeatKernel

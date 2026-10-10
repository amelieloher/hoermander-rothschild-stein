-- Copyright (c) 2026 Scott Armstrong and Amélie Loher. All rights reserved.
-- Released under Apache 2.0 license as described in the file LICENSE.
module

public import HeatKernel.Semigroup.HorizontalTimeDerivative
public import Mathlib.Analysis.InnerProductSpace.Calculus
public import Mathlib.MeasureTheory.Integral.IntervalIntegral.FundThmCalculus

/-! # The heat flow as a vector in the energy form domain -/

@[expose] public section
noncomputable section
open MeasureTheory Set TopologicalSpace
namespace HeatKernel
variable {N q : ℕ} (X : Fin q → (Fin N → ℝ) → (Fin N → ℝ))

/-- The form-domain representative obtained from the adjoint inclusion. -/
def horizontalHeatFormVector (f : SpatialL2 (N := N) ⊤) (t : ℝ) : energyGraph ⊤ X :=
  ContinuousLinearMap.adjoint (𝕜 := ℝ) (E := energyGraph ⊤ X) (F := SpatialL2 ⊤)
    (energyInclusion ⊤ X)
    (horizontalHeatOperator ⊤ X t.toNNReal f + horizontalHeatGeneratorOperator ⊤ X t f)

theorem energyInclusion_horizontalHeatFormVector (f : SpatialL2 (N := N) ⊤)
    {t : ℝ} (ht : 0 < t) :
    energyInclusion ⊤ X (horizontalHeatFormVector X f t) =
      horizontalHeatOperator ⊤ X t.toNNReal f :=
  horizontalHeatOperator_generator_equation ⊤ X t ht f

theorem horizontalEnergy_horizontalHeatFormVector
    (hX : ∀ i, ContDiff ℝ (⊤ : ℕ∞) (X i)) (f : SpatialL2 (N := N) ⊤)
    {t : ℝ} (ht : 0 < t) (v : energyGraph ⊤ X) :
    horizontalEnergy ⊤ X (horizontalHeatFormVector X f t) v =
      inner ℝ (horizontalHeatGeneratorOperator ⊤ X t f) (energyInclusion ⊤ X v) := by
  apply (horizontalFormEquation_iff_resolvent_eq ⊤ X
    (fun i => (hX i).contDiffOn) (horizontalHeatFormVector X f t) _).mpr ?_ v
  rw [energyInclusion_horizontalHeatFormVector X f ht]
  exact horizontalHeatOperator_generator_equation ⊤ X t ht f

end HeatKernel

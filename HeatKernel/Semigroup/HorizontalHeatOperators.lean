-- Copyright (c) 2026 Scott Armstrong and Amélie Loher. All rights reserved.
-- Released under Apache 2.0 license as described in the file LICENSE.
module

public import HeatKernel.Semigroup.RealL2HeatGenerator
public import HeatKernel.Form.GraphForm
public import RothschildStein.G2.InvariantDivergence
public import HeatKernel.Semigroup.HorizontalOperatorGraph
public import RothschildStein.Definitions.HomogeneousGroup.horizontalFields_contDiff

/-! # Heat operators associated with the horizontal form

The form resolvent gives concrete heat operators on spatial real L². Their generator acts
on smooth tests as the negative horizontal sum of squares.
-/

@[expose] public section
noncomputable section
open MeasureTheory Set Filter TopologicalSpace RothschildStein
open scoped ENNReal NNReal Topology
namespace HeatKernel
variable {N q : ℕ} (U : Opens (Fin N → ℝ))
    (X : Fin q → (Fin N → ℝ) → (Fin N → ℝ))

/-- Heat operators constructed from the horizontal energy resolvent. -/
def horizontalHeatOperator (t : ℝ≥0) : SpatialL2 U →L[ℝ] SpatialL2 U :=
  realL2HeatOperator (volume.restrict (U : Set (Fin N → ℝ))) (horizontalFormResolvent U X)
    (horizontalFormResolvent_isPositive U X) (norm_horizontalFormResolvent_le_one U X) t

theorem horizontalHeatOperator_zero : horizontalHeatOperator U X 0 = 1 :=
  realL2HeatOperator_zero _ _ _ _

theorem horizontalHeatOperator_add (s t : ℝ≥0) :
    horizontalHeatOperator U X (s + t) =
      horizontalHeatOperator U X s * horizontalHeatOperator U X t :=
  realL2HeatOperator_add _ _ _ _ s t

theorem norm_horizontalHeatOperator_le_one (t : ℝ≥0) :
    ‖horizontalHeatOperator U X t‖ ≤ 1 := norm_realL2HeatOperator_le_one _ _ _ _ t

theorem horizontalHeatOperator_isSelfAdjoint (t : ℝ≥0) :
    IsSelfAdjoint (horizontalHeatOperator U X t) := realL2HeatOperator_isSelfAdjoint _ _ _ _ t

theorem continuous_horizontalHeatOperator_univ_apply
    (hX : ∀ i, ContDiff ℝ (⊤ : ℕ∞) (X i)) (f : SpatialL2 (N := N) ⊤) :
    Continuous (fun t : ℝ≥0 => horizontalHeatOperator ⊤ X t f) :=
  continuous_realL2HeatOperator_apply _ _ _ _ (horizontalFormResolvent_univ_injective X hX) f

theorem tendsto_horizontalHeatOperator_univ_differenceQuotient_iff
    (hX : ∀ i, ContDiff ℝ (⊤ : ℕ∞) (X i)) (u g : SpatialL2 (N := N) ⊤) :
    Tendsto (fun t : ℝ => t⁻¹ • (horizontalHeatOperator ⊤ X t.toNNReal u - u))
      (𝓝[>] 0) (𝓝 (-g)) ↔ horizontalFormResolvent ⊤ X (u + g) = u :=
  tendsto_realL2HeatOperator_differenceQuotient_iff _ _ _ _
    (horizontalFormResolvent_univ_injective X hX) u g

end HeatKernel

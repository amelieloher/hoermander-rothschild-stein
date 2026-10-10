-- Copyright (c) 2026 Scott Armstrong and Amélie Loher. All rights reserved.
-- Released under Apache 2.0 license as described in the file LICENSE.
module

public import HeatKernel.Semigroup.RealL2PositiveTimeDomain
public import HeatKernel.Semigroup.HorizontalHeatOperators

/-! # Horizontal heat vectors in the form operator domain -/

@[expose] public section
noncomputable section
open MeasureTheory Set Filter TopologicalSpace
open scoped Topology
namespace HeatKernel
variable {N q : ℕ} (U : Opens (Fin N → ℝ))
    (X : Fin q → (Fin N → ℝ) → (Fin N → ℝ))

/-- The bounded horizontal generator after evolution for positive time. -/
def horizontalHeatGeneratorOperator (t : ℝ) : SpatialL2 U →L[ℝ] SpatialL2 U :=
  realL2HeatGeneratorOperator (volume.restrict (U : Set (Fin N → ℝ)))
    (horizontalFormResolvent U X) t

theorem horizontalHeatOperator_generator_equation (t : ℝ) (ht : 0 < t) (f : SpatialL2 U) :
    horizontalFormResolvent U X
      (horizontalHeatOperator U X t.toNNReal f + horizontalHeatGeneratorOperator U X t f) =
      horizontalHeatOperator U X t.toNNReal f :=
  realL2HeatOperator_generator_equation _ _ (horizontalFormResolvent_isPositive U X)
    (norm_horizontalFormResolvent_le_one U X) t ht f

theorem horizontalHeatOperator_mem_operatorGraph (t : ℝ) (ht : 0 < t) (f : SpatialL2 U) :
    InverseResolventGraph (horizontalFormResolvent U X)
      (horizontalHeatOperator U X t.toNNReal f) (horizontalHeatGeneratorOperator U X t f) :=
  (inverseResolventGraph_iff _ _ _).mpr (horizontalHeatOperator_generator_equation U X t ht f)

theorem tendsto_horizontalHeatOperator_positiveTime_differenceQuotient
    (hX : ∀ i, ContDiff ℝ (⊤ : ℕ∞) (X i))
    (t : ℝ) (ht : 0 < t) (f : SpatialL2 (N := N) ⊤) :
    Tendsto (fun s : ℝ => s⁻¹ •
      (horizontalHeatOperator ⊤ X s.toNNReal (horizontalHeatOperator ⊤ X t.toNNReal f) -
        horizontalHeatOperator ⊤ X t.toNNReal f))
      (𝓝[>] 0) (𝓝 (-horizontalHeatGeneratorOperator ⊤ X t f)) :=
  (tendsto_horizontalHeatOperator_univ_differenceQuotient_iff X hX _ _).mpr
    (horizontalHeatOperator_generator_equation ⊤ X t ht f)

end HeatKernel

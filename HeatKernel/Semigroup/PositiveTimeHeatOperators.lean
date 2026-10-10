-- Copyright (c) 2026 Scott Armstrong and Amélie Loher. All rights reserved.
-- Released under Apache 2.0 license as described in the file LICENSE.
module

public import HeatKernel.Semigroup.OperatorEulerApproximation
public import HeatKernel.Semigroup.ScaledResolventCfc
public import HeatKernel.Semigroup.PositiveTimeDomain

/-! # Positive-time heat operators and Euler limits -/

@[expose] public section
noncomputable section
open Set Filter
open scoped Topology
namespace HeatKernel
variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℂ E] [CompleteSpace E]

/-- The continuous heat multiplier, evaluated by functional calculus. -/
def positiveTimeHeatOperator (R : E →L[ℂ] E) (t : ℝ) : E →L[ℂ] E :=
  cfc (heatMultiplier t) R

theorem heatOperator_toNNReal_of_pos (R : E →L[ℂ] E) {t : ℝ} (ht : 0 < t) :
    heatOperator R t.toNNReal = positiveTimeHeatOperator R t := by
  unfold heatOperator positiveTimeHeatOperator
  congr 1
  funext r
  rw [semigroupMultiplier_of_pos (Real.toNNReal_pos.mpr ht), Real.coe_toNNReal t ht.le]

theorem tendsto_scaledResolventCfcOperator_pow (R : E →L[ℂ] E) (hR : IsSelfAdjoint R)
    (hspec : spectrum ℝ R ⊆ Icc (0 : ℝ) 1) {t : ℝ} (ht : 0 < t) :
    Tendsto (fun n : ℕ => scaledResolventCfcOperator R (t / n) ^ n) atTop
      (𝓝 (positiveTimeHeatOperator R t)) :=
  tendsto_resolventMultiplier_cfc_pow R hR hspec ht

theorem positiveTimeHeatOperator_generator_equation (R : E →L[ℂ] E)
    (hR : IsSelfAdjoint R) (t : ℝ) (f : E) :
    R (positiveTimeHeatOperator R t f + heatGeneratorOperator R t f) =
      positiveTimeHeatOperator R t f :=
  heat_cfc_generator_resolvent_equation_apply R hR t f

end HeatKernel

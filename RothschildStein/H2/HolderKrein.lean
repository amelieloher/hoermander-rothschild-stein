-- Copyright (c) 2026 Scott Armstrong and Amélie Loher. All rights reserved.
-- Released under Apache 2.0 license as described in the file LICENSE.
module

public import RothschildStein.H2.HolderL2Density
public import RothschildStein.H2.Krein
public import Mathlib.Analysis.Normed.Operator.Extend

@[expose] public section
set_option autoImplicit false
set_option relaxedAutoImplicit false
noncomputable section
open Set MeasureTheory Metric
open scoped NNReal ENNReal

namespace RothschildStein.H2
variable {X : Type*} [MetricSpace X] [MeasurableSpace X] [BorelSpace X]

/-- Krein applied to the actual dense Hölder module, with its L²
inner product and its finite Hölder seminorm. This helper records the
algebraic operator hypotheses used by the Data D assembly. -/
theorem holder_krein_bound (D : LocDoubling X) {δ : ℝ≥0} {U : Set X}
    (hδ : 0 < δ) (hU : IsOpen U) (hU₁ : U ⊆ D.Ω₁) (hμ : D.μ U < ⊤)
    (T T' : holderFunctions δ U →ₗ[ℝ] holderFunctions δ U) {a b : ℝ}
    (ha : 0 ≤ a) (hb : 0 ≤ b)
    (hT : ∀ f, holderFunctionSeminorm δ U (T f) ≤ a * holderFunctionSeminorm δ U f)
    (hT' : ∀ f, holderFunctionSeminorm δ U (T' f) ≤ b * holderFunctionSeminorm δ U f)
    (hadj : ∀ f g, inner ℝ (holderL2 δ U D.μ hδ hU.measurableSet hμ (T f))
      (holderL2 δ U D.μ hδ hU.measurableSet hμ g) =
      inner ℝ (holderL2 δ U D.μ hδ hU.measurableSet hμ f)
        (holderL2 δ U D.μ hδ hU.measurableSet hμ (T' g)))
    (f : holderFunctions δ U) :
    ‖holderL2 δ U D.μ hδ hU.measurableSet hμ (T f)‖ ≤
      Real.sqrt (a * b) * ‖holderL2 δ U D.μ hδ hU.measurableSet hμ f‖ := by
  let e := holderL2 δ U D.μ hδ hU.measurableSet hμ
  let : NormedAddCommGroup (holderFunctions δ U) :=
    NormedAddCommGroup.induced _ _ e (holderL2_injective D hδ hU hU₁ hμ)
  let : InnerProductSpace ℝ (holderFunctions δ U) := InnerProductSpace.induced e
  exact krein_norm_bound (holderFunctionSeminorm δ U) T T'
    (ENNReal.toReal_nonneg (a := D.μ U ^ (1 / 2 : ℝ))) ha hb
    (holderL2_norm_le hδ hU.measurableSet hμ) hT hT' hadj f

end RothschildStein.H2

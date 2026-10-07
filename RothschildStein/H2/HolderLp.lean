-- Copyright (c) 2026 Scott Armstrong and Amélie Loher. All rights reserved.
-- Released under Apache 2.0 license as described in the file LICENSE.
module
public import RothschildStein.H2.HolderL2Density
public import RothschildStein.H2.LpIntersection
@[expose] public section
set_option autoImplicit false
set_option relaxedAutoImplicit false
noncomputable section
open Set MeasureTheory Metric
open scoped NNReal ENNReal
namespace RothschildStein.H2
variable {X : Type*} [MetricSpace X] [MeasurableSpace X] [BorelSpace X]

/-- Bounded Hölder representatives on a finite patch belong to every Lᵖ. -/
theorem BoundedHolder.memLp {μ : Measure X} {δ : ℝ≥0} {U : Set X} {f : X → ℝ}
    (hf : BoundedHolder δ U f) (hδ : 0 < δ) (hU : MeasurableSet U)
    (hμ : μ U < ⊤) (p : ℝ≥0∞) : MemLp f p (μ.restrict U) := by
  let : IsFiniteMeasure (μ.restrict U) := ⟨by simpa using hμ⟩
  exact MemLp.of_bound (hf.aestronglyMeasurable_restrict hδ hU)
    (holderSup U f).toReal (by
      filter_upwards [ae_restrict_mem hU] with x hx
      simpa only [Real.norm_eq_abs] using abs_le_holderSup hf.parts.1 hx)

/-- The concrete dense Hölder domain mapped into Lᵖ. -/
def holderLp (δ : ℝ≥0) (U : Set X) (μ : Measure X)
    (hδ : 0 < δ) (hU : MeasurableSet U) (hμ : μ U < ⊤) (p : ℝ≥0∞) [Fact (1 ≤ p)] :
    holderFunctions δ U →ₗ[ℝ] Lp ℝ p (μ.restrict U) where
  toFun f := (f.property.1.memLp hδ hU hμ p).toLp f
  map_add' _ _ := MemLp.toLp_add _ _
  map_smul' c _ := MemLp.toLp_const_smul c _

end RothschildStein.H2

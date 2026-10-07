-- Copyright (c) 2026 Scott Armstrong and Amélie Loher. All rights reserved.
-- Released under Apache 2.0 license as described in the file LICENSE.
module

public import RothschildStein.H2.HolderModule

set_option autoImplicit false
set_option relaxedAutoImplicit false
@[expose] public section
noncomputable section
namespace RothschildStein.H3
open Set Metric MeasureTheory
open scoped NNReal ENNReal
variable {X : Type*} [MetricSpace X] [MeasurableSpace X] [BorelSpace X]

/-- Bounded Holder functions belong to every Lp space on a finite
patch. This is the actual embedding used in fixed-operator agreement. -/
theorem boundedHolder_memLp {μ : Measure X} {δ : ℝ≥0} {U : Set X} {f : X → ℝ}
    (hf : H2.BoundedHolder δ U f) (hδ : 0 < δ) (hU : MeasurableSet U)
    (hμ : μ U < ⊤) (p : ℝ≥0∞) : MemLp f p (μ.restrict U) := by
  let : IsFiniteMeasure (μ.restrict U) := ⟨by simpa using hμ⟩
  exact MemLp.of_bound (hf.aestronglyMeasurable_restrict hδ hU) (H2.holderSup U f).toReal
    (by filter_upwards [ae_restrict_mem hU] with x hx
        simpa only [Real.norm_eq_abs] using H2.abs_le_holderSup hf.parts.1 hx)

/-- The Lp class of a normalized bounded Holder representative. -/
def holderLp (μ : Measure X) (p : ℝ≥0∞) {δ : ℝ≥0} {U : Set X}
    (hδ : 0 < δ) (hU : MeasurableSet U) (hμ : μ U < ⊤)
    (f : H2.holderFunctions δ U) : Lp ℝ p (μ.restrict U) :=
  (boundedHolder_memLp f.property.1 hδ hU hμ p).toLp f

/-- The Lp embedding has the given representative almost everywhere. -/
theorem holderLp_coe_ae (μ : Measure X) (p : ℝ≥0∞) {δ : ℝ≥0} {U : Set X}
    (hδ : 0 < δ) (hU : MeasurableSet U) (hμ : μ U < ⊤)
    (f : H2.holderFunctions δ U) :
    (holderLp μ p hδ hU hμ f : X → ℝ) =ᵐ[μ.restrict U] (f : X → ℝ) :=
  (boundedHolder_memLp f.property.1 hδ hU hμ p).coeFn_toLp

end RothschildStein.H3

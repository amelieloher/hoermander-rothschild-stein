-- Copyright (c) 2026 Scott Armstrong and Amélie Loher. All rights reserved.
-- Released under Apache 2.0 license as described in the file LICENSE.
module
public import RothschildStein.H2.DataDLpPair
public import RothschildStein.H2.HolderLp
@[expose] public section
set_option autoImplicit false
set_option relaxedAutoImplicit false
noncomputable section
open Set MeasureTheory Metric
open scoped ENNReal NNReal
namespace RothschildStein.H2
variable {X : Type*} [MetricSpace X] [MeasurableSpace X] [BorelSpace X]

/-- The Hölder Lᵖ embedding also lies in L² on the finite patch. -/
theorem holderLp_memLp_two {μ : Measure X} {δ : ℝ≥0} {U : Set X}
    (hδ : 0 < δ) (hU : MeasurableSet U) (hμ : μ U < ⊤)
    (p : ℝ≥0∞) [Fact (1 ≤ p)] (f : holderFunctions δ U) :
    MemLp (holderLp δ U μ hδ hU hμ p f) 2 (μ.restrict U) :=
  (memLp_congr_ae (f.property.1.memLp hδ hU hμ p).coeFn_toLp).mpr
    (f.property.1.memLp_two hδ hU hμ)

/-- Conversion of a Hölder Lᵖ representative recovers its existing L² class. -/
theorem lpL2ToL2_holderLp {μ : Measure X} {δ : ℝ≥0} {U : Set X}
    (hδ : 0 < δ) (hU : MeasurableSet U) (hμ : μ U < ⊤)
    (p : ℝ≥0∞) [Fact (1 ≤ p)] (f : holderFunctions δ U) :
    lpL2ToL2 (μ.restrict U) p
      ⟨holderLp δ U μ hδ hU hμ p f, holderLp_memLp_two hδ hU hμ p f⟩ =
        holderL2 δ U μ hδ hU hμ f := by
  apply Lp.ext
  exact (holderLp_memLp_two hδ hU hμ p f).coeFn_toLp.trans
    ((f.property.1.memLp hδ hU hμ p).coeFn_toLp.trans
      (f.property.1.memLp_two hδ hU hμ).coeFn_toLp.symm)

variable {D : LocDoubling X} {d : TruncDist D}
/-- The extension agrees with the fixed-gauge principal value
on every concrete Hölder input; this is not a separate consistency assumption. -/
theorem DataDLpPair.apply_principalValue {Q : LocalKernelData D d} {P : TransposeData Q}
    {δ : ℝ≥0} {hδ : 0 < δ} {hδ₀ : (δ : ℝ) < Q.β₀} {hδβ : (δ : ℝ) < Q.β}
    {hδν : (δ : ℝ) < Q.ν} {hδ₀' : (δ : ℝ) < P.data.β₀}
    {hδβ' : (δ : ℝ) < P.data.β} {hδν' : (δ : ℝ) < P.data.ν}
    {m p : ℝ} [Fact (1 ≤ ENNReal.ofReal p)]
    [Fact (1 ≤ ENNReal.ofReal (Real.conjExponent p))]
    (L : DataDLpPair P hδ hδ₀ hδβ hδν hδ₀' hδβ' hδν' m p)
    (f : holderFunctions δ (ball Q.z Q.R)) :
    L.operator (holderLp δ (ball Q.z Q.R) D.μ hδ isOpen_ball.measurableSet
      Q.measure_ball_lt_top (ENNReal.ofReal p) f) =ᵐ[D.μ.restrict (ball Q.z Q.R)]
        Q.principalValue f := by
  have he := L.consistency
    ⟨holderLp δ (ball Q.z Q.R) D.μ hδ isOpen_ball.measurableSet Q.measure_ball_lt_top _ f,
      holderLp_memLp_two hδ isOpen_ball.measurableSet Q.measure_ball_lt_top _ f⟩
  rw [lpL2ToL2_holderLp,
    P.l2Operator_apply hδ hδ₀ hδβ hδν hδ₀' hδβ' hδν'] at he
  refine he.trans ?_
  filter_upwards [(Q.principalValueHolderOperator hδ hδ₀ hδβ hδν f).property.1.memLp_two
    hδ isOpen_ball.measurableSet Q.measure_ball_lt_top |>.coeFn_toLp,
    ae_restrict_mem isOpen_ball.measurableSet] with x hx hxu
  exact hx.trans (Q.principalValueHolderOperator_apply hδ hδ₀ hδβ hδν f hxu)
end RothschildStein.H2

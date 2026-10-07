-- Copyright (c) 2026 Scott Armstrong and Amélie Loher. All rights reserved.
-- Released under Apache 2.0 license as described in the file LICENSE.
module

public import RothschildStein.H3.L2ExponentIndependence
public import RothschildStein.H3.HolderLp
public import RothschildStein.H2.LpIntersection

set_option autoImplicit false
set_option relaxedAutoImplicit false
@[expose] public section
noncomputable section
namespace RothschildStein.H3
open Set Metric MeasureTheory
open scoped NNReal ENNReal
variable {X : Type*} [MetricSpace X] [MeasurableSpace X] [BorelSpace X]
variable {D : H2.LocDoubling X} {d : H2.TruncDist D}

/-- A fixed Lp extension of the L2 principal value agrees with the
pointwise principal value on every allowed bounded Holder class. Exponent
independence follows from uniqueness on a common dense domain and bounded
ball embeddings; no approximation sequence is an input. -/
theorem lp_agrees_principalValue_of_l2_consistency {Q : H2.LocalKernelData D d}
    (P : H2.TransposeData Q) (p : ℝ≥0∞) [Fact (1 ≤ p)]
    (Tp : Lp ℝ p (D.μ.restrict (ball Q.z Q.R)) →L[ℝ]
      Lp ℝ p (D.μ.restrict (ball Q.z Q.R)))
    {s : ℝ≥0} (hs : 0 < s)
    (hs₀ : (s : ℝ) < Q.β₀) (hsβ : (s : ℝ) < Q.β) (hsν : (s : ℝ) < Q.ν)
    (hs₀' : (s : ℝ) < P.data.β₀) (hsβ' : (s : ℝ) < P.data.β) (hsν' : (s : ℝ) < P.data.ν)
    (hcons : ∀ v : H2.lpL2Intersection (D.μ.restrict (ball Q.z Q.R)) p,
      (fun x => (Tp (v : Lp ℝ p (D.μ.restrict (ball Q.z Q.R)))) x)
        =ᵐ[D.μ.restrict (ball Q.z Q.R)]
        fun x => (P.l2Operator hs hs₀ hsβ hsν hs₀' hsβ' hsν'
          (H2.lpL2ToL2 (D.μ.restrict (ball Q.z Q.R)) p v)) x)
    {δ : ℝ≥0} (hδ : 0 < δ)
    (hδ₀ : (δ : ℝ) < Q.β₀) (hδβ : (δ : ℝ) < Q.β) (hδν : (δ : ℝ) < Q.ν)
    (hδ₀' : (δ : ℝ) < P.data.β₀) (hδβ' : (δ : ℝ) < P.data.β) (hδν' : (δ : ℝ) < P.data.ν)
    (f : H2.holderFunctions δ (ball Q.z Q.R)) :
    (fun x => (Tp (holderLp D.μ p hδ isOpen_ball.measurableSet Q.measure_ball_lt_top f)) x)
      =ᵐ[D.μ.restrict (ball Q.z Q.R)] Q.principalValue f := by
  have hfLp := holderLp_coe_ae D.μ p hδ isOpen_ball.measurableSet Q.measure_ball_lt_top f
  have hf2 := f.property.1.memLp_two hδ isOpen_ball.measurableSet Q.measure_ball_lt_top
  have hv : MemLp
      (holderLp D.μ p hδ isOpen_ball.measurableSet Q.measure_ball_lt_top f : X → ℝ)
      2 (D.μ.restrict (ball Q.z Q.R)) := (memLp_congr_ae hfLp).mpr hf2
  let v : H2.lpL2Intersection (D.μ.restrict (ball Q.z Q.R)) p :=
    ⟨holderLp D.μ p hδ isOpen_ball.measurableSet Q.measure_ball_lt_top f, hv⟩
  have hv2 : H2.lpL2ToL2 (D.μ.restrict (ball Q.z Q.R)) p v =
      H2.holderL2 δ (ball Q.z Q.R) D.μ hδ isOpen_ball.measurableSet Q.measure_ball_lt_top f := by
    apply Lp.ext
    filter_upwards [hv.coeFn_toLp, hf2.coeFn_toLp, hfLp] with x hx hx2 hxp
    exact hx.trans (hxp.trans hx2.symm)
  have hi := l2Operator_independent_exponent P hs hs₀ hsβ hsν hs₀' hsβ' hsν'
    hδ hδ₀ hδβ hδν hδ₀' hδβ' hδν'
  have hc := hcons v
  rw [hi, hv2, P.l2Operator_apply hδ hδ₀ hδβ hδν hδ₀' hδβ' hδν' f] at hc
  let g := Q.principalValueHolderOperator hδ hδ₀ hδβ hδν f
  have hg := (g.property.1.memLp_two hδ isOpen_ball.measurableSet Q.measure_ball_lt_top).coeFn_toLp
  filter_upwards [hc, hg, ae_restrict_mem isOpen_ball.measurableSet] with x hx hxg hxU
  exact hx.trans (hxg.trans (Q.principalValueHolderOperator_apply hδ hδ₀ hδβ hδν f hxU))

end RothschildStein.H3

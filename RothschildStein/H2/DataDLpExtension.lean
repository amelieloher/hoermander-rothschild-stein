-- Copyright (c) 2026 Scott Armstrong and Amélie Loher. All rights reserved.
-- Released under Apache 2.0 license as described in the file LICENSE.
module
public import RothschildStein.H2.DataDL2Certificate
public import RothschildStein.H2.LocalOperatorPairExtension
public import RothschildStein.H2.UniformVolume
@[expose] public section
set_option autoImplicit false
set_option relaxedAutoImplicit false
noncomputable section
open Set MeasureTheory Metric
open scoped ENNReal NNReal
namespace RothschildStein.H2
variable {X : Type*} [MetricSpace X] [MeasurableSpace X] [BorelSpace X]
variable {D : LocDoubling X} {d : TruncDist D}

/-- Each partition piece has a conjugate-space extension and an associated L² operator. -/
theorem TransposeData.lp_extensions {Q : LocalKernelData D d} (P : TransposeData Q)
    {δ : ℝ≥0} (hδ : 0 < δ) (hδ₀ : (δ : ℝ) < Q.β₀) (hδβ : (δ : ℝ) < Q.β)
    (hδν : (δ : ℝ) < Q.ν) (hδ₀' : (δ : ℝ) < P.data.β₀)
    (hδβ' : (δ : ℝ) < P.data.β) (hδν' : (δ : ℝ) < P.data.ν)
    {m p : ℝ} (hm : 0 < m)
    (hml : ∀ z ∈ D.Ω₁, ENNReal.ofReal m ≤ D.μ (ball z D.κ))
    (hp : 1 < p) [Fact (1 ≤ ENNReal.ofReal p)]
    [Fact (1 ≤ ENNReal.ofReal (Real.conjExponent p))] :
    let μ := D.μ.restrict (ball Q.z Q.R)
    let C := 2 * nonnegativeWeakConstant D (min P.data.β₀ P.data.β)
      P.data.singularS (P.l2Constant δ) m
    let Cs := 2 * nonnegativeWeakConstant D (min Q.β₀ Q.β)
      Q.singularS (P.l2Constant δ) m
    ∃ Tp Tsp : Lp ℝ (ENNReal.ofReal p) μ →L[ℝ] Lp ℝ (ENNReal.ofReal p) μ,
    ∃ Tsq : Lp ℝ (ENNReal.ofReal (Real.conjExponent p)) μ →L[ℝ]
        Lp ℝ (ENNReal.ofReal (Real.conjExponent p)) μ,
      ‖Tp‖ + ‖Tsp‖ ≤ operatorAllExponentConstant C Cs (P.l2Constant δ) p +
        operatorAllExponentConstant Cs C (P.l2Constant δ) p ∧
      (∀ v : lpL2Intersection μ (ENNReal.ofReal p),
        (Tp (v : Lp ℝ (ENNReal.ofReal p) μ)) =ᵐ[μ]
          P.l2Operator hδ hδ₀ hδβ hδν hδ₀' hδβ' hδν' (lpL2ToL2 μ _ v)) ∧
      (∀ v : lpL2Intersection μ (ENNReal.ofReal p),
        (Tsp (v : Lp ℝ (ENNReal.ofReal p) μ)) =ᵐ[μ]
          P.transposeL2Operator hδ hδ₀ hδβ hδν hδ₀' hδβ' hδν' (lpL2ToL2 μ _ v)) ∧
      (∀ v : lpL2Intersection μ (ENNReal.ofReal (Real.conjExponent p)),
        (Tsq (v : Lp ℝ (ENNReal.ofReal (Real.conjExponent p)) μ)) =ᵐ[μ]
          P.transposeL2Operator hδ hδ₀ hδβ hδν hδ₀' hδβ' hδν' (lpL2ToL2 μ _ v)) ∧
      (∀ f g, (∫ x, (Tp f) x * g x ∂μ) = ∫ x, f x * (Tsq g) x ∂μ) := by
  apply D.operator_pair_extension_of_l2_certificate Q.center
    ((ball_subset_ball (by linarith [Q.radius_pos])).trans Q.doubledBall_subset) Q.radius_lt
    (P.l2Operator hδ hδ₀ hδβ hδν hδ₀' hδβ' hδν')
    (P.transposeL2Operator hδ hδ₀ hδβ hδν hδ₀' hδβ' hδν')
    (P.l2Certificate hδ hδ₀ hδβ hδν hδ₀' hδβ' hδν')
    (P.transposeL2Certificate hδ hδ₀ hδβ hδν hδ₀' hδβ' hδν')
    _ hm hml hp
  intro v w
  simpa only [L2.inner_def, Real.inner_apply] using
    P.l2Operator_adjoint hδ hδ₀ hδβ hδν hδ₀' hδβ' hδν' v w
end RothschildStein.H2

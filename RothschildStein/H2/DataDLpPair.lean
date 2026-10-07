-- Copyright (c) 2026 Scott Armstrong and Amélie Loher. All rights reserved.
-- Released under Apache 2.0 license as described in the file LICENSE.
module
public import RothschildStein.H2.DataDLpExtension
@[expose] public section
set_option autoImplicit false
set_option relaxedAutoImplicit false
noncomputable section
open Set MeasureTheory Metric
open scoped ENNReal NNReal
namespace RothschildStein.H2
variable {X : Type*} [MetricSpace X] [MeasurableSpace X] [BorelSpace X]
variable {D : LocDoubling X} {d : TruncDist D}

/-- The explicit upper bound for the local extension. -/
def TransposeData.lpConstant {Q : LocalKernelData D d} (P : TransposeData Q)
    (δ : ℝ) (m p : ℝ) : ℝ :=
  let C := 2 * nonnegativeWeakConstant D (min P.data.β₀ P.data.β)
    P.data.singularS (P.l2Constant δ) m
  let Cs := 2 * nonnegativeWeakConstant D (min Q.β₀ Q.β)
    Q.singularS (P.l2Constant δ) m
  operatorAllExponentConstant C Cs (P.l2Constant δ) p +
    operatorAllExponentConstant Cs C (P.l2Constant δ) p

/-- A concrete pair of conjugate-space local extensions, retaining
consistency with the actual principal-value L² operator. -/
structure DataDLpPair {Q : LocalKernelData D d} (P : TransposeData Q)
    {δ : ℝ≥0} (hδ : 0 < δ) (hδ₀ : (δ : ℝ) < Q.β₀) (hδβ : (δ : ℝ) < Q.β)
    (hδν : (δ : ℝ) < Q.ν) (hδ₀' : (δ : ℝ) < P.data.β₀)
    (hδβ' : (δ : ℝ) < P.data.β) (hδν' : (δ : ℝ) < P.data.ν)
    (m p : ℝ) [Fact (1 ≤ ENNReal.ofReal p)]
    [Fact (1 ≤ ENNReal.ofReal (Real.conjExponent p))] where
  operator : Lp ℝ (ENNReal.ofReal p) (D.μ.restrict (ball Q.z Q.R)) →L[ℝ]
    Lp ℝ (ENNReal.ofReal p) (D.μ.restrict (ball Q.z Q.R))
  transposeOperator : Lp ℝ (ENNReal.ofReal (Real.conjExponent p))
    (D.μ.restrict (ball Q.z Q.R)) →L[ℝ]
    Lp ℝ (ENNReal.ofReal (Real.conjExponent p)) (D.μ.restrict (ball Q.z Q.R))
  norm_le : ‖operator‖ ≤ P.lpConstant δ m p
  consistency : ∀ v : lpL2Intersection (D.μ.restrict (ball Q.z Q.R)) (ENNReal.ofReal p),
    operator (v : Lp ℝ (ENNReal.ofReal p) (D.μ.restrict (ball Q.z Q.R))) =ᵐ[D.μ.restrict (ball Q.z Q.R)]
      P.l2Operator hδ hδ₀ hδβ hδν hδ₀' hδβ' hδν'
        (lpL2ToL2 (D.μ.restrict (ball Q.z Q.R)) _ v)
  adjoint : ∀ v w, (∫ x, (operator v) x * w x ∂D.μ.restrict (ball Q.z Q.R)) =
    ∫ x, v x * (transposeOperator w) x ∂D.μ.restrict (ball Q.z Q.R)

/-- A local extension pair for the transpose data. -/
theorem TransposeData.exists_lpPair {Q : LocalKernelData D d} (P : TransposeData Q)
    {δ : ℝ≥0} (hδ : 0 < δ) (hδ₀ : (δ : ℝ) < Q.β₀) (hδβ : (δ : ℝ) < Q.β)
    (hδν : (δ : ℝ) < Q.ν) (hδ₀' : (δ : ℝ) < P.data.β₀)
    (hδβ' : (δ : ℝ) < P.data.β) (hδν' : (δ : ℝ) < P.data.ν)
    {m p : ℝ} (hm : 0 < m)
    (hml : ∀ z ∈ D.Ω₁, ENNReal.ofReal m ≤ D.μ (ball z D.κ))
    (hp : 1 < p) [Fact (1 ≤ ENNReal.ofReal p)]
    [Fact (1 ≤ ENNReal.ofReal (Real.conjExponent p))] :
    Nonempty (DataDLpPair P hδ hδ₀ hδβ hδν hδ₀' hδβ' hδν' m p) := by
  obtain ⟨T, Tsp, Ts, hb, hT, _, _, hadj⟩ :=
    P.lp_extensions hδ hδ₀ hδβ hδν hδ₀' hδβ' hδν' hm hml hp
  exact ⟨⟨T, Ts, (le_add_of_nonneg_right (norm_nonneg Tsp)).trans hb, hT, hadj⟩⟩
end RothschildStein.H2

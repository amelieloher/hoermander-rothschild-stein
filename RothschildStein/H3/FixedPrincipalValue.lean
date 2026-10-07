-- Copyright (c) 2026 Scott Armstrong and Amélie Loher. All rights reserved.
-- Released under Apache 2.0 license as described in the file LICENSE.
module

public import RothschildStein.H3.FixedLocalLp
public import RothschildStein.H3.LpPrincipalValueAgreement
public import RothschildStein.H3.LocalizedPrincipalValue

set_option autoImplicit false
set_option relaxedAutoImplicit false
@[expose] public section
noncomputable section
namespace RothschildStein.H3
open Set Metric MeasureTheory Filter
open scoped NNReal ENNReal Topology

/-- The fixed local Lp realization agrees with the pointwise
principal value at every Holder exponent in (0,1), with the same operator
norm bound. The pointwise limits and Holder estimate use the original and
transpose truncated-kernel bounds (BB Theorem 8.22, pp. 357–359). Agreement
follows from uniqueness on a common higher-exponent dense domain. -/
theorem fixedPrincipalValue_of_truncatedKernelFacts {N : ℕ} (G : HomogeneousGroup N)
    (ν : G2.HomogeneousNorm G) (h1 : ν.c = 1) (hsym : ν.Symmetric)
    (A S : ℝ) (K : ControlCarrier N → ControlCarrier N → ℝ)
    (H : letI := gaugeMetric G ν h1 hsym; TruncatedKernelFacts volume A S K)
    (Ht : letI := gaugeMetric G ν h1 hsym
      TruncatedKernelFacts volume A S (fun x y => K y x))
    {p : ℝ} (hp : 1 < p) [Fact (1 ≤ ENNReal.ofReal p)] :
    letI := gaugeMetric G ν h1 hsym
    let Q := localKernelData_of_truncatedKernelFacts G ν h1 hsym A S K H
    let P := localTransposeData_of_truncatedKernelFacts G ν h1 hsym A S K H Ht
    ∃ Tp : Lp ℝ (ENNReal.ofReal p) (volume.restrict (ball (0 : ControlCarrier N) 2)) →L[ℝ]
        Lp ℝ (ENNReal.ofReal p) (volume.restrict (ball (0 : ControlCarrier N) 2)),
      ‖Tp‖ ≤ localLpConstant G ν h1 hsym Q.singularS (P.l2Constant realizationExponent) p ∧
      ∀ (δ : ℝ≥0) (hδ : 0 < δ), (δ : ℝ) < 1 →
        ∀ f : H2.holderFunctions δ (ball (0 : ControlCarrier N) 2),
          ((fun x => (Tp (holderLp volume (ENNReal.ofReal p) hδ
            isOpen_ball.measurableSet Q.measure_ball_lt_top f)) x)
              =ᵐ[volume.restrict (ball (0 : ControlCarrier N) 2)] Q.principalValue f) ∧
          (∀ x ∈ ball (0 : ControlCarrier N) 2,
            Tendsto (fun ε : ℝ => H2.truncatedIntegral volume (ball 0 2)
              dist Q.cutoffKernel ε f x) (𝓝[>] 0) (𝓝 (Q.principalValue f x))) ∧
          H2.boundedHolderNorm δ (ball (0 : ControlCarrier N) 2) (Q.principalValue f) ≤
            ENNReal.ofReal (Q.operatorHolderConstant δ) *
              H2.boundedHolderNorm δ (ball (0 : ControlCarrier N) 2) f := by
  let := gaugeMetric G ν h1 hsym
  let Q := localKernelData_of_truncatedKernelFacts G ν h1 hsym A S K H
  let P := localTransposeData_of_truncatedKernelFacts G ν h1 hsym A S K H Ht
  obtain ⟨Tp, hnorm, hcons⟩ := fixedLocalLp_of_truncatedKernelFacts G ν h1 hsym A S K H Ht hp
  refine ⟨Tp, hnorm, ?_⟩
  intro δ hδ hδ1 f
  have hag := lp_agrees_principalValue_of_l2_consistency P (ENNReal.ofReal p) Tp
    realizationExponent_bounds.1 realizationExponent_bounds.2 realizationExponent_bounds.2
    realizationExponent_bounds.2 realizationExponent_bounds.2 realizationExponent_bounds.2
    realizationExponent_bounds.2 hcons hδ hδ1 hδ1 hδ1 hδ1 hδ1 hδ1 f
  exact ⟨hag, local_principalValue_holder_of_truncatedKernelFacts G ν h1 hsym A S K H
    hδ hδ1 f.property.1⟩

end RothschildStein.H3

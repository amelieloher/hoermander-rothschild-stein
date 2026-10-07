-- Copyright (c) 2026 Scott Armstrong and Amélie Loher. All rights reserved.
-- Released under Apache 2.0 license as described in the file LICENSE.
module

public import RothschildStein.H3.FixedLocalL2
public import RothschildStein.H3.LocalLpRealization

set_option autoImplicit false
set_option relaxedAutoImplicit false
@[expose] public section
noncomputable section
namespace RothschildStein.H3
open Set Metric MeasureTheory
open scoped ENNReal
variable {N : ℕ} (G : HomogeneousGroup N)

/-- The fixed bounded local Lp realization uses the local L2 extension
and the scaled truncated-kernel bounds. Its definition at exponent one
half makes the operator independent of the Holder
exponent subsequently used to evaluate its pointwise principal value.
BB Theorem 8.22, proof pp. 357–359. -/
theorem fixedLocalLp_of_truncatedKernelFacts (ν : G2.HomogeneousNorm G)
    (h1 : ν.c = 1) (hsym : ν.Symmetric) (A S : ℝ)
    (K : ControlCarrier N → ControlCarrier N → ℝ)
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
      (∀ v : H2.lpL2Intersection (volume.restrict (ball (0 : ControlCarrier N) 2))
          (ENNReal.ofReal p),
        (fun x => (Tp (v : Lp ℝ (ENNReal.ofReal p)
            (volume.restrict (ball (0 : ControlCarrier N) 2)))) x)
          =ᵐ[volume.restrict (ball (0 : ControlCarrier N) 2)]
          fun x => (fixedLocalL2Operator G ν h1 hsym A S K H Ht
            (H2.lpL2ToL2 (volume.restrict (ball (0 : ControlCarrier N) 2))
              (ENNReal.ofReal p) v)) x) := by
  let := gaugeMetric G ν h1 hsym
  let Q := localKernelData_of_truncatedKernelFacts G ν h1 hsym A S K H
  obtain ⟨hT, hTs, hadj⟩ := fixedLocalL2_certificates_of_truncatedKernelFacts G ν h1 hsym A S K H Ht
  exact local_lp_realization G ν h1 hsym hp Q.cutoffKernel
    (fixedLocalL2Operator G ν h1 hsym A S K H Ht)
    (fixedTransposeLocalL2Operator G ν h1 hsym A S K H Ht) hT hTs hadj

end RothschildStein.H3

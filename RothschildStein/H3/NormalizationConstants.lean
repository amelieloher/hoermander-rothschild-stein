-- Copyright (c) 2026 Scott Armstrong and Amélie Loher. All rights reserved.
-- Released under Apache 2.0 license as described in the file LICENSE.
module

public import RothschildStein.H3.KernelNormalization
public import RothschildStein.H3.FixedPrincipalValueBound

set_option autoImplicit false
set_option relaxedAutoImplicit false
@[expose] public section
noncomputable section
namespace RothschildStein.H3
open Set Metric MeasureTheory
open scoped ENNReal

/-- The normalized Lp constant depends on the geometry, p, and the
fixed geometric kernel bounds A and S. It contains no kernel or seminorm. -/
def normalizedLocalLpConstant {N : ℕ} (G : HomogeneousGroup N)
    (ν : G2.HomogeneousNorm G) (h1 : ν.c = 1) (hsym : ν.Symmetric)
    (A S : ℝ) (hA : 0 ≤ A) (hS : 0 ≤ S) (p : ℝ) : ℝ := by
  let := gaugeMetric G ν h1 hsym
  let H0 := truncatedKernelFacts_zero (volume : Measure (ControlCarrier N)) hA hS
  let Q0 := localKernelData_of_truncatedKernelFacts G ν h1 hsym A S (fun _ _ => 0) H0
  let P0 := localTransposeData_of_truncatedKernelFacts G ν h1 hsym A S (fun _ _ => 0) H0 H0
  exact localLpConstant G ν h1 hsym Q0.singularS (P0.l2Constant realizationExponent) p

/-- The numeric norm bound of the fixed realization is independent
of the kernel whenever its size and smoothness bounds are fixed. -/
theorem localLpConstant_eq_normalized {N : ℕ} (G : HomogeneousGroup N)
    (ν : G2.HomogeneousNorm G) (h1 : ν.c = 1) (hsym : ν.Symmetric)
    (A S : ℝ) (hA : 0 ≤ A) (hS : 0 ≤ S)
    (K : ControlCarrier N → ControlCarrier N → ℝ)
    (H : letI := gaugeMetric G ν h1 hsym; TruncatedKernelFacts volume A S K)
    (Ht : letI := gaugeMetric G ν h1 hsym
      TruncatedKernelFacts volume A S (fun x y => K y x)) (p : ℝ) :
    letI := gaugeMetric G ν h1 hsym
    let Q := localKernelData_of_truncatedKernelFacts G ν h1 hsym A S K H
    let P := localTransposeData_of_truncatedKernelFacts G ν h1 hsym A S K H Ht
    localLpConstant G ν h1 hsym Q.singularS (P.l2Constant realizationExponent) p =
      normalizedLocalLpConstant G ν h1 hsym A S hA hS p := by
  rfl

/-- The normalized Holder coefficient likewise depends only on
geometry and the fixed kernel bounds, retaining the input exponent. -/
def normalizedLocalHolderConstant {N : ℕ} (G : HomogeneousGroup N)
    (ν : G2.HomogeneousNorm G) (h1 : ν.c = 1) (hsym : ν.Symmetric)
    (A S : ℝ) (hA : 0 ≤ A) (hS : 0 ≤ S) (δ : ℝ) : ℝ := by
  let := gaugeMetric G ν h1 hsym
  let H0 := truncatedKernelFacts_zero (volume : Measure (ControlCarrier N)) hA hS
  exact (localKernelData_of_truncatedKernelFacts G ν h1 hsym A S (fun _ _ => 0) H0).operatorHolderConstant δ

/-- The Holder coefficient has no dependence on the particular
kernel after its size and smoothness bounds have been fixed. -/
theorem localHolderConstant_eq_normalized {N : ℕ} (G : HomogeneousGroup N)
    (ν : G2.HomogeneousNorm G) (h1 : ν.c = 1) (hsym : ν.Symmetric)
    (A S : ℝ) (hA : 0 ≤ A) (hS : 0 ≤ S)
    (K : ControlCarrier N → ControlCarrier N → ℝ)
    (H : letI := gaugeMetric G ν h1 hsym; TruncatedKernelFacts volume A S K) (δ : ℝ) :
    letI := gaugeMetric G ν h1 hsym
    (localKernelData_of_truncatedKernelFacts G ν h1 hsym A S K H).operatorHolderConstant δ =
      normalizedLocalHolderConstant G ν h1 hsym A S hA hS δ := by
  rfl

end RothschildStein.H3

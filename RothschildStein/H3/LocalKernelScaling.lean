-- Copyright (c) 2026 Scott Armstrong and Amélie Loher. All rights reserved.
-- Released under Apache 2.0 license as described in the file LICENSE.
module

public import RothschildStein.H3.KernelScalingLimits

set_option autoImplicit false
set_option relaxedAutoImplicit false
@[expose] public section
noncomputable section
namespace RothschildStein.H3
open Set Metric MeasureTheory
open scoped NNReal ENNReal

/-- The complete localized kernel scales with the kernel seminorm;
the geometric cutoffs and the integration ball are identical. -/
theorem localCutoffKernel_normalize {N : ℕ} (G : HomogeneousGroup N)
    (ν : G2.HomogeneousNorm G) (h1 : ν.c = 1) (hsym : ν.Symmetric)
    (A S Λ : ℝ) (hΛ : 0 < Λ) (K : ControlCarrier N → ControlCarrier N → ℝ)
    (H : letI := gaugeMetric G ν h1 hsym
      TruncatedKernelFacts volume (Λ * A) (Λ * S) K) :
    letI := gaugeMetric G ν h1 hsym
    let Hn := truncatedKernelFacts_normalize hΛ H
    let Q := localKernelData_of_truncatedKernelFacts G ν h1 hsym (Λ * A) (Λ * S) K H
    let Qn := localKernelData_of_truncatedKernelFacts G ν h1 hsym A S (fun x y => Λ⁻¹ * K x y) Hn
    Q.cutoffKernel = fun x y => Λ * Qn.cutoffKernel x y := by
  classical
  let := gaugeMetric G ν h1 hsym
  let a := localizationCutoff (0 : ControlCarrier N)
  funext x y
  change (if x ∈ ball (0 : ControlCarrier N) 2 ∧ y ∈ ball (0 : ControlCarrier N) 2
    then a x * (K x y + 0) * a y else 0) =
    Λ * (if x ∈ ball (0 : ControlCarrier N) 2 ∧ y ∈ ball (0 : ControlCarrier N) 2
      then a x * (Λ⁻¹ * K x y + 0) * a y else 0)
  split_ifs
  · simp only [add_zero]
    field_simp
  · simp

/-- The actual principal-value formula scales by the seminorm on
its entire local domain. This follows from the certified truncation limits,
so no linearity assumption about a chosen extension is used. -/
theorem localPrincipalValue_normalize {N : ℕ} (G : HomogeneousGroup N)
    (ν : G2.HomogeneousNorm G) (h1 : ν.c = 1) (hsym : ν.Symmetric)
    (A S Λ : ℝ) (hΛ : 0 < Λ) (K : ControlCarrier N → ControlCarrier N → ℝ)
    (H : letI := gaugeMetric G ν h1 hsym
      TruncatedKernelFacts volume (Λ * A) (Λ * S) K)
    {δ : ℝ≥0} (hδ : 0 < δ) (hδ1 : (δ : ℝ) < 1)
    (f : ControlCarrier N → ℝ)
    (hf : letI := gaugeMetric G ν h1 hsym
      H2.BoundedHolder δ (ball (0 : ControlCarrier N) 2) f) :
    letI := gaugeMetric G ν h1 hsym
    let Hn := truncatedKernelFacts_normalize hΛ H
    let Q := localKernelData_of_truncatedKernelFacts G ν h1 hsym (Λ * A) (Λ * S) K H
    let Qn := localKernelData_of_truncatedKernelFacts G ν h1 hsym A S (fun x y => Λ⁻¹ * K x y) Hn
    EqOn (Q.principalValue f) (fun x => Λ * Qn.principalValue f x)
      (ball (0 : ControlCarrier N) 2) := by
  let := gaugeMetric G ν h1 hsym
  let Hn := truncatedKernelFacts_normalize hΛ H
  let Q := localKernelData_of_truncatedKernelFacts G ν h1 hsym (Λ * A) (Λ * S) K H
  let Qn := localKernelData_of_truncatedKernelFacts G ν h1 hsym A S (fun x y => Λ⁻¹ * K x y) Hn
  dsimp only
  intro x hx
  exact principalValue_scale_of_limits volume (ball (0 : ControlCarrier N) 2) dist
    Q.cutoffKernel Qn.cutoffKernel Λ (localCutoffKernel_normalize G ν h1 hsym A S Λ hΛ K H)
    f x ((local_principalValue_holder_of_truncatedKernelFacts G ν h1 hsym (Λ * A) (Λ * S) K H
      hδ hδ1 hf).1 x hx)
    ((local_principalValue_holder_of_truncatedKernelFacts G ν h1 hsym A S (fun x y => Λ⁻¹ * K x y) Hn
      hδ hδ1 hf).1 x hx)

end RothschildStein.H3

-- Copyright (c) 2026 Scott Armstrong and Amélie Loher. All rights reserved.
-- Released under Apache 2.0 license as described in the file LICENSE.
module

public import RothschildStein.H3.LocalKernelScaling

set_option autoImplicit false
set_option relaxedAutoImplicit false
@[expose] public section
noncomputable section
namespace RothschildStein.H3
open Set Metric MeasureTheory Filter
open scoped NNReal ENNReal Topology
variable {X : Type*} [MetricSpace X] [MeasurableSpace X]

/-- A zero size bound forces the kernel to vanish off the diagonal.
No value at the diagonal is required. -/
theorem kernel_eq_zero_of_size_zero {μ : Measure X} {β ν S : ℝ} {K : X → X → ℝ}
    (H : H2.KernelClass μ univ β ν 0 S K) {x y : X} (hxy : x ≠ y) : K x y = 0 := by
  have hh := H.size x (mem_univ _) y (mem_univ _) hxy
  have ha : |K x y| ≤ 0 := by simpa only [zero_mul] using hh
  exact abs_eq_zero.mp (le_antisymm ha (abs_nonneg _))

/-- Every positive truncation of a kernel vanishing off the diagonal
is exactly zero. In particular a diagonal value cannot affect a limit. -/
theorem truncatedIntegral_zero_of_off_diagonal (μ : Measure X) (U : Set X)
    (K : X → X → ℝ) (hK : ∀ x y, x ≠ y → K x y = 0)
    {ε : ℝ} (hε : 0 < ε) (f : X → ℝ) (x : X) :
    H2.truncatedIntegral μ U dist K ε f x = 0 := by
  unfold H2.truncatedIntegral
  apply setIntegral_eq_zero_of_forall_eq_zero
  intro y hy
  have hxy : x ≠ y := by
    intro he
    have hd : ε < dist x y := hy.2
    rw [he, dist_self] at hd
    exact (hε.trans hd).false
  simp only [hK x y hxy, zero_mul]

/-- The principal value is zero on the integration ball when the
truncated-kernel size constant is zero. -/
theorem localPrincipalValue_zero_of_truncatedKernelFacts {N : ℕ} (G : HomogeneousGroup N)
    (ν : G2.HomogeneousNorm G) (h1 : ν.c = 1) (hsym : ν.Symmetric)
    (K : ControlCarrier N → ControlCarrier N → ℝ)
    (H : letI := gaugeMetric G ν h1 hsym; TruncatedKernelFacts volume 0 0 K)
    {δ : ℝ≥0} (hδ : 0 < δ) (hδ1 : (δ : ℝ) < 1)
    (f : ControlCarrier N → ℝ)
    (hf : letI := gaugeMetric G ν h1 hsym
      H2.BoundedHolder δ (ball (0 : ControlCarrier N) 2) f) :
    letI := gaugeMetric G ν h1 hsym
    let Q := localKernelData_of_truncatedKernelFacts G ν h1 hsym 0 0 K H
    EqOn (Q.principalValue f) (fun _ => 0) (ball (0 : ControlCarrier N) 2) := by
  classical
  let := gaugeMetric G ν h1 hsym
  let Q := localKernelData_of_truncatedKernelFacts G ν h1 hsym 0 0 K H
  have hK : ∀ x y, x ≠ y → Q.cutoffKernel x y = 0 := by
    intro x y hxy
    change H2.localizedKernel (ball (0 : ControlCarrier N) 2)
      (localizationCutoff 0) (localizationCutoff 0) (fun x y => K x y + 0) x y = 0
    unfold H2.localizedKernel
    split_ifs <;> simp only [kernel_eq_zero_of_size_zero H.kernel hxy, add_zero, mul_zero, zero_mul]
  dsimp only
  intro x hx
  have hlim := (local_principalValue_holder_of_truncatedKernelFacts G ν h1 hsym 0 0 K H hδ hδ1 hf).1 x hx
  have he : (fun ε : ℝ => H2.truncatedIntegral volume (ball (0 : ControlCarrier N) 2)
      dist Q.cutoffKernel ε f x) =ᶠ[𝓝[>] 0] (fun _ => (0 : ℝ)) := by
    filter_upwards [self_mem_nhdsWithin] with ε hε
    exact truncatedIntegral_zero_of_off_diagonal volume (ball (0 : ControlCarrier N) 2)
      Q.cutoffKernel hK hε f x
  exact tendsto_nhds_unique hlim (tendsto_const_nhds.congr' he.symm)

end RothschildStein.H3

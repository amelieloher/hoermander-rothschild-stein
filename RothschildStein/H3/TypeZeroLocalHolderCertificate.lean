-- Copyright (c) 2026 Scott Armstrong and Amélie Loher. All rights reserved.
-- Released under Apache 2.0 license as described in the file LICENSE.
module

public import RothschildStein.H3.TypeZeroGeometricCertificate
public import RothschildStein.H3.NormalizedPrincipalValueNonnegative

set_option autoImplicit false
set_option relaxedAutoImplicit false
set_option backward.isDefEq.respectTransparency false
@[expose] public section
noncomputable section
open Set Metric MeasureTheory Filter
open scoped Topology NNReal ENNReal
namespace RothschildStein.H3

/-- The actual type-zero radial truncation has pointwise PV
limits and a uniform local Hölder bound linear in its first seminorm.
No truncated-kernel certificate is supplied as a hypothesis. -/
theorem exists_typeZero_local_holder_certificate_of_controlNorm {N q : ℕ}
    (G : HomogeneousGroup N)
    {Y : Fin (q + 1) → (Fin N → ℝ) → (Fin N → ℝ)}
    (C : G2.ControlNormConclusion G driftWeight Y)
    (hY : ∀ i, ContinuousOn (Y i) {0}ᶜ)
    (hhomY : ∀ i, G2.IsHomogeneousField G (Y i) (if i = 0 then 2 else 1)) :
    let _metric : MetricSpace (ControlCarrier N) :=
      gaugeMetric G C.norm C.constant_one C.symmetric
    ∃ (A S : ℝ) (hA : 0 ≤ A) (hS : 0 ≤ S),
      ∀ (k : (Fin N → ℝ) → ℝ), TypeZero G C.norm k →
      ∃ HK : TruncatedKernelFacts volume (kernelDerivativeBound C.norm k 1 * A)
        (kernelDerivativeBound C.norm k 1 * S)
        (fun x y : ControlCarrier N => truncatedKernel G C.norm k x y),
      let Q := localKernelData_of_truncatedKernelFacts G C.norm C.constant_one C.symmetric
        (kernelDerivativeBound C.norm k 1 * A) (kernelDerivativeBound C.norm k 1 * S)
        (fun x y : ControlCarrier N => truncatedKernel G C.norm k x y) HK
      ∀ (δ : ℝ≥0), 0 < δ → (δ : ℝ) < 1 →
      ∀ (f : ControlCarrier N → ℝ), H2.BoundedHolder δ (ball (0 : ControlCarrier N) 2) f →
      (∀ x ∈ ball (0 : ControlCarrier N) 2,
        Tendsto (fun ε : ℝ => H2.truncatedIntegral volume (ball 0 2)
          dist Q.cutoffKernel ε f x) (𝓝[>] 0) (𝓝 (Q.principalValue f x))) ∧
      H2.boundedHolderNorm δ (ball (0 : ControlCarrier N) 2) (Q.principalValue f) ≤
        ENNReal.ofReal (kernelDerivativeBound C.norm k 1 *
          normalizedLocalHolderConstant G C.norm C.constant_one C.symmetric A S hA hS δ) *
          H2.boundedHolderNorm δ (ball (0 : ControlCarrier N) 2) f := by
  let _metric : MetricSpace (ControlCarrier N) :=
    gaugeMetric G C.norm C.constant_one C.symmetric
  let _hpFact : Fact (1 ≤ ENNReal.ofReal (2 : ℝ)) := ⟨by norm_num⟩
  obtain ⟨A, S, hA, hS, hcert⟩ :=
    exists_typeZero_geometric_truncated_certificates_of_controlNorm G C hY hhomY
  refine ⟨A, S, hA, hS, ?_⟩
  intro k hk
  obtain ⟨HK, HKt⟩ := hcert k hk
  refine ⟨HK, ?_⟩
  obtain ⟨_, _, hagree⟩ := normalizedPrincipalValue_nonnegative_of_truncatedKernelFacts G C.norm
    C.constant_one C.symmetric A S hA hS (kernelDerivativeBound C.norm k 1)
    (kernelDerivativeBound_properties C.norm.gauge hk.smooth 1).1
    (fun x y : ControlCarrier N => truncatedKernel G C.norm k x y) HK HKt
    (show (1 : ℝ) < 2 by norm_num)
  dsimp only
  intro δ hδ hδ1 f hf
  exact (hagree δ hδ hδ1 f hf).2.2

end RothschildStein.H3

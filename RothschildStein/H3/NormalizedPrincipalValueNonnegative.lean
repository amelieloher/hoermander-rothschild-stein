-- Copyright (c) 2026 Scott Armstrong and Amélie Loher. All rights reserved.
-- Released under Apache 2.0 license as described in the file LICENSE.
module

public import RothschildStein.H3.NormalizedPrincipalValue
public import RothschildStein.H3.ZeroPrincipalValue

set_option autoImplicit false
set_option relaxedAutoImplicit false
@[expose] public section
noncomputable section
namespace RothschildStein.H3
open Set Metric MeasureTheory Filter
open scoped NNReal ENNReal Topology

/-- Seminorm normalization including the zero case gives one fixed operator with
norm linear in Lambda, agreement on every bounded Holder class, pointwise
limits, and both Lp and Holder estimates. The coefficients depend only on
geometry, p, the fixed geometric kernel bounds A and S, and (for the Holder
estimate) delta. It assumes the scaled truncated-kernel bounds.
BB Theorem 8.22, pp. 357–359. -/
theorem normalizedPrincipalValue_nonnegative_of_truncatedKernelFacts {N : ℕ} (G : HomogeneousGroup N)
    (ν : G2.HomogeneousNorm G) (h1 : ν.c = 1) (hsym : ν.Symmetric)
    (A S : ℝ) (hA : 0 ≤ A) (hS : 0 ≤ S)
    (Λ : ℝ) (hΛ : 0 ≤ Λ) (K : ControlCarrier N → ControlCarrier N → ℝ)
    (H : letI := gaugeMetric G ν h1 hsym
      TruncatedKernelFacts volume (Λ * A) (Λ * S) K)
    (Ht : letI := gaugeMetric G ν h1 hsym
      TruncatedKernelFacts volume (Λ * A) (Λ * S) (fun x y => K y x))
    {p : ℝ} (hp : 1 < p) [Fact (1 ≤ ENNReal.ofReal p)] :
    letI := gaugeMetric G ν h1 hsym
    let Q := localKernelData_of_truncatedKernelFacts G ν h1 hsym (Λ * A) (Λ * S) K H
    let C := normalizedLocalLpConstant G ν h1 hsym A S hA hS p
    ∃ Tp : Lp ℝ (ENNReal.ofReal p) (volume.restrict (ball (0 : ControlCarrier N) 2)) →L[ℝ]
        Lp ℝ (ENNReal.ofReal p) (volume.restrict (ball (0 : ControlCarrier N) 2)),
      ‖Tp‖ ≤ Λ * C ∧
      ∀ (δ : ℝ≥0) (hδ : 0 < δ), (δ : ℝ) < 1 →
        ∀ (f : ControlCarrier N → ℝ)
          (hf : H2.BoundedHolder δ (ball (0 : ControlCarrier N) 2) f),
          ((fun x => (Tp (holderLp volume (ENNReal.ofReal p) hδ
            isOpen_ball.measurableSet Q.measure_ball_lt_top (H2.holderNormalize hf))) x)
              =ᵐ[volume.restrict (ball (0 : ControlCarrier N) 2)] Q.principalValue f) ∧
          (eLpNorm (Q.principalValue f) (ENNReal.ofReal p) (volume.restrict (ball 0 2)) ≤
            ENNReal.ofReal (Λ * C) * eLpNorm f (ENNReal.ofReal p)
              (volume.restrict (ball 0 2))) ∧
          (∀ x ∈ ball (0 : ControlCarrier N) 2,
            Tendsto (fun ε : ℝ => H2.truncatedIntegral volume (ball 0 2)
              dist Q.cutoffKernel ε f x) (𝓝[>] 0) (𝓝 (Q.principalValue f x))) ∧
          H2.boundedHolderNorm δ (ball (0 : ControlCarrier N) 2) (Q.principalValue f) ≤
            ENNReal.ofReal (Λ * normalizedLocalHolderConstant G ν h1 hsym A S hA hS δ) *
              H2.boundedHolderNorm δ (ball (0 : ControlCarrier N) 2) f := by
  by_cases hpos : 0 < Λ
  · exact normalizedPrincipalValue_of_truncatedKernelFacts G ν h1 hsym A S hA hS Λ hpos K H Ht hp
  have heq : Λ = 0 := le_antisymm (le_of_not_gt hpos) hΛ
  subst Λ
  simp only [zero_mul, ENNReal.ofReal_zero] at H Ht ⊢
  let := gaugeMetric G ν h1 hsym
  let Q := localKernelData_of_truncatedKernelFacts G ν h1 hsym 0 0 K H
  refine ⟨0, by simp, ?_⟩
  intro δ hδ hδ1 f hf
  have hzero := localPrincipalValue_zero_of_truncatedKernelFacts G ν h1 hsym K H hδ hδ1 f hf
  have hzAE : Q.principalValue f =ᵐ[volume.restrict (ball (0 : ControlCarrier N) 2)]
      (fun _ => (0 : ℝ)) := by
    filter_upwards [ae_restrict_mem isOpen_ball.measurableSet] with x hx
    exact hzero hx
  have hout : (fun x => ((0 : Lp ℝ (ENNReal.ofReal p)
      (volume.restrict (ball (0 : ControlCarrier N) 2))) x))
      =ᵐ[volume.restrict (ball (0 : ControlCarrier N) 2)] Q.principalValue f :=
    (Lp.coeFn_zero ℝ (ENNReal.ofReal p) (volume.restrict (ball (0 : ControlCarrier N) 2))).trans
      hzAE.symm
  refine ⟨hout, ?_, (local_principalValue_holder_of_truncatedKernelFacts G ν h1 hsym 0 0 K H hδ hδ1 hf).1, ?_⟩
  · rw [eLpNorm_congr_ae hzAE]
    simp
  · rw [H2.boundedHolderNorm_congr hzero]
    simp [H2.boundedHolderNorm, H2.holderSup, H2.holderSemi]
    exact eHolderNorm_const _ δ (0 : ℝ)

end RothschildStein.H3

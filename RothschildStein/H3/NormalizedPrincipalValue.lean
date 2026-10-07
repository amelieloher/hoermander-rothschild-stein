-- Copyright (c) 2026 Scott Armstrong and Amélie Loher. All rights reserved.
-- Released under Apache 2.0 license as described in the file LICENSE.
module

public import RothschildStein.H3.NormalizationConstants
public import RothschildStein.H3.LocalKernelScaling

set_option autoImplicit false
set_option relaxedAutoImplicit false
@[expose] public section
noncomputable section
namespace RothschildStein.H3
open Set Metric MeasureTheory Filter
open scoped NNReal ENNReal Topology

/-- Positive-seminorm normalization gives one fixed operator with
norm linear in Lambda, agreement on every bounded Holder class, pointwise
limits, and both Lp and Holder estimates. The coefficients depend only on
geometry, p, the fixed geometric kernel bounds A and S, and (for the Holder
estimate) delta. It assumes the scaled truncated-kernel bounds.
BB Theorem 8.22, pp. 357–359. -/
theorem normalizedPrincipalValue_of_truncatedKernelFacts {N : ℕ} (G : HomogeneousGroup N)
    (ν : G2.HomogeneousNorm G) (h1 : ν.c = 1) (hsym : ν.Symmetric)
    (A S : ℝ) (hA : 0 ≤ A) (hS : 0 ≤ S)
    (Λ : ℝ) (hΛ : 0 < Λ) (K : ControlCarrier N → ControlCarrier N → ℝ)
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
  let := gaugeMetric G ν h1 hsym
  let Kn := fun x y => Λ⁻¹ * K x y
  let Hn := truncatedKernelFacts_normalize hΛ H
  let Hnt := truncatedKernelFacts_normalize hΛ Ht
  let Q := localKernelData_of_truncatedKernelFacts G ν h1 hsym (Λ * A) (Λ * S) K H
  let Qn := localKernelData_of_truncatedKernelFacts G ν h1 hsym A S Kn Hn
  let C := normalizedLocalLpConstant G ν h1 hsym A S hA hS p
  obtain ⟨Tn, hnorm, hagree⟩ := fixedPrincipalValue_bound_of_truncatedKernelFacts G ν h1 hsym A S Kn Hn Hnt hp
  have hnormn : ‖Tn‖ ≤ C := by
    simpa only [localLpConstant_eq_normalized G ν h1 hsym A S hA hS Kn Hn Hnt p] using hnorm
  let Tp := Λ • Tn
  have hnormp : ‖Tp‖ ≤ Λ * C := by
    calc
      ‖Tp‖ = |Λ| * ‖Tn‖ := norm_smul Λ Tn
      _ ≤ Λ * C := by rw [abs_of_pos hΛ]; exact mul_le_mul_of_nonneg_left hnormn hΛ.le
  refine ⟨Tp, hnormp, ?_⟩
  intro δ hδ hδ1 f hf
  obtain ⟨ha, _, _, hholder⟩ := hagree δ hδ hδ1 f hf
  have hscale := localPrincipalValue_normalize G ν h1 hsym A S Λ hΛ K H hδ hδ1 f hf
  let v := holderLp volume (ENNReal.ofReal p) hδ isOpen_ball.measurableSet
    Q.measure_ball_lt_top (H2.holderNormalize hf)
  have hout : (fun x => (Tp v) x) =ᵐ[volume.restrict (ball (0 : ControlCarrier N) 2)]
      Q.principalValue f := by
    have hs := Lp.coeFn_smul Λ (Tn v)
    filter_upwards [hs, ha, ae_restrict_mem isOpen_ball.measurableSet] with x hx hxA hxU
    exact hx.trans ((congrArg (fun t : ℝ => Λ * t) hxA).trans (hscale hxU).symm)
  have hin := (holderNormalize_domain Q hδ hf (ENNReal.ofReal p)).1
  have hnormf := eLpNorm_bound_of_operator_agreement Tp hnormp v hin hout
  have hlim := (local_principalValue_holder_of_truncatedKernelFacts G ν h1 hsym
    (Λ * A) (Λ * S) K H hδ hδ1 hf).1
  refine ⟨hout, hnormf, hlim, ?_⟩
  rw [H2.boundedHolderNorm_congr hscale]
  change H2.boundedHolderNorm δ (ball (0 : ControlCarrier N) 2) (Λ • Qn.principalValue f) ≤ _
  rw [H2.boundedHolderNorm_smul, abs_of_pos hΛ]
  have hn : H2.boundedHolderNorm δ (ball (0 : ControlCarrier N) 2) (Qn.principalValue f) ≤
      ENNReal.ofReal (normalizedLocalHolderConstant G ν h1 hsym A S hA hS δ) *
        H2.boundedHolderNorm δ (ball (0 : ControlCarrier N) 2) f := by
    simpa only [localHolderConstant_eq_normalized G ν h1 hsym A S hA hS Kn Hn δ] using hholder
  calc
    ENNReal.ofReal Λ * H2.boundedHolderNorm δ (ball (0 : ControlCarrier N) 2)
        (Qn.principalValue f) ≤ ENNReal.ofReal Λ *
          (ENNReal.ofReal (normalizedLocalHolderConstant G ν h1 hsym A S hA hS δ) *
            H2.boundedHolderNorm δ (ball (0 : ControlCarrier N) 2) f) := by gcongr
    _ = _ := by rw [ENNReal.ofReal_mul hΛ.le, mul_assoc]

end RothschildStein.H3

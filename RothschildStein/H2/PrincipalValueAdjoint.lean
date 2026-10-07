-- Copyright (c) 2026 Scott Armstrong and Amélie Loher. All rights reserved.
-- Released under Apache 2.0 license as described in the file LICENSE.
module

public import RothschildStein.H2.TruncatedAdjoint
public import RothschildStein.H2.TruncatedHolderBound
public import Mathlib.MeasureTheory.Integral.DominatedConvergence

@[expose] public section
set_option autoImplicit false
set_option relaxedAutoImplicit false
noncomputable section
open Set MeasureTheory Metric Filter
open scoped ENNReal NNReal Topology

namespace RothschildStein.H2
variable {X : Type*} [MetricSpace X] [MeasurableSpace X] [BorelSpace X]
variable {D : LocDoubling X} {d : TruncDist D}

/-- Passing a bounded Hölder pairing to the PV limit by DCT. -/
theorem LocalKernelData.tendsto_integral_truncated_mul (Q : LocalKernelData D d)
    {δ : ℝ≥0} (hδ : 0 < δ) {f g : X → ℝ}
    (hf : BoundedHolder δ (ball Q.z Q.R) f) (hg : BoundedHolder δ (ball Q.z Q.R) g) :
    Tendsto (fun ε : ℝ => ∫ x in ball Q.z Q.R,
      truncatedIntegral D.μ (ball Q.z Q.R) d.d' Q.cutoffKernel ε f x * g x ∂D.μ)
      (𝓝[>] 0) (𝓝 (∫ x in ball Q.z Q.R, Q.principalValue f x * g x ∂D.μ)) := by
  have hfin : D.μ (ball Q.z Q.R) < ⊤ :=
    (measure_mono (Q.supported_localized_singular.sub_G.trans D.sub₁₂)).trans_lt D.finΩ₂
  let : IsFiniteMeasure (D.μ.restrict (ball Q.z Q.R)) := ⟨by simpa using hfin⟩
  let B := Q.singularA * (holderSemi δ (ball Q.z Q.R) f).toReal *
    volumeIntegralConstant D.C_D δ * (2 * Q.R) ^ (δ : ℝ) +
      Q.cancellationConstant * (holderSup (ball Q.z Q.R) f).toReal
  have hB : 0 ≤ B := add_nonneg
    (mul_nonneg (mul_nonneg (mul_nonneg Q.localized_singular.A_nonneg ENNReal.toReal_nonneg)
      (volumeIntegralConstant_pos (C := D.C_D) (by linarith [D.one_lt_C_D]) hδ).le)
      (Real.rpow_nonneg (by linarith [Q.radius_pos]) _))
    (mul_nonneg Q.cancellationConstant_nonneg ENNReal.toReal_nonneg)
  apply tendsto_integral_filter_of_dominated_convergence
    (fun _ => B * (holderSup (ball Q.z Q.R) g).toReal)
  · filter_upwards [self_mem_nhdsWithin] with ε hε
    exact (Q.truncated_aestronglyMeasurable hδ hf hε).mul
      (hg.aestronglyMeasurable_restrict hδ isOpen_ball.measurableSet)
  · filter_upwards [self_mem_nhdsWithin] with ε hε
    filter_upwards [ae_restrict_mem isOpen_ball.measurableSet] with x hx
    rw [Real.norm_eq_abs, abs_mul]
    exact mul_le_mul (Q.truncated_abs_le hδ hf hε hx)
      (abs_le_holderSup hg.parts.1 hx) (abs_nonneg _) hB
  · exact integrable_const _
  · filter_upwards [ae_restrict_mem isOpen_ball.measurableSet] with x hx
    exact (Q.principalValue_limit hδ hf hx).mul_const (g x)

/-- The two principal-value operators are adjoints on the dense Hölder class when the cutoffs are exchanged. -/
theorem TransposeData.principalValue_adjoint {Q : LocalKernelData D d} (P : TransposeData Q)
    {δ : ℝ≥0} (hδ : 0 < δ) {f g : X → ℝ}
    (hf : BoundedHolder δ (ball Q.z Q.R) f) (hg : BoundedHolder δ (ball Q.z Q.R) g) :
    (∫ x in ball Q.z Q.R, Q.principalValue f x * g x ∂D.μ) =
      ∫ x in ball Q.z Q.R, f x * P.data.principalValue g x ∂D.μ := by
  have hfp : BoundedHolder δ (ball P.data.z P.data.R) f := by simpa only [P.centre, P.radius] using hf
  have hgp : BoundedHolder δ (ball P.data.z P.data.R) g := by simpa only [P.centre, P.radius] using hg
  have hl := Q.tendsto_integral_truncated_mul hδ hf hg
  have hr := P.data.tendsto_integral_truncated_mul hδ hgp hfp
  simp only [P.centre, P.radius] at hr
  have hright : Tendsto (fun ε : ℝ => ∫ x in ball Q.z Q.R,
      f x * truncatedIntegral D.μ (ball Q.z Q.R) d.d' P.data.cutoffKernel ε g x ∂D.μ)
      (𝓝[>] 0) (𝓝 (∫ x in ball Q.z Q.R, f x * P.data.principalValue g x ∂D.μ)) := by
    simpa only [mul_comm] using hr
  have he : (fun ε : ℝ => ∫ x in ball Q.z Q.R,
      truncatedIntegral D.μ (ball Q.z Q.R) d.d' Q.cutoffKernel ε f x * g x ∂D.μ) =ᶠ[𝓝[>] 0]
      (fun ε : ℝ => ∫ x in ball Q.z Q.R,
      f x * truncatedIntegral D.μ (ball Q.z Q.R) d.d' P.data.cutoffKernel ε g x ∂D.μ) := by
    filter_upwards [self_mem_nhdsWithin] with ε hε
    exact P.truncated_adjoint hδ hf hg hε
  exact tendsto_nhds_unique hl (hright.congr' he.symm)

end RothschildStein.H2

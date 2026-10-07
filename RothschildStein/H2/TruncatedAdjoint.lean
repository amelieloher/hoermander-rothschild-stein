-- Copyright (c) 2026 Scott Armstrong and Amélie Loher. All rights reserved.
-- Released under Apache 2.0 license as described in the file LICENSE.
module

public import RothschildStein.H2.TruncatedKernel
public import RothschildStein.H2.BoundedKernelMeasurable
public import RothschildStein.H2.HolderLinear

@[expose] public section
set_option autoImplicit false
set_option relaxedAutoImplicit false
noncomputable section
open Set MeasureTheory Metric
open scoped ENNReal NNReal

namespace RothschildStein.H2
variable {X : Type*} [MetricSpace X] [MeasurableSpace X] [BorelSpace X]
variable {D : LocDoubling X} {d : TruncDist D}

/-- Positive truncated PV actions are measurable in the outer variable. -/
theorem LocalKernelData.truncated_aestronglyMeasurable (Q : LocalKernelData D d)
    {δ : ℝ≥0} (hδ : 0 < δ) {f : X → ℝ} (hf : BoundedHolder δ (ball Q.z Q.R) f)
    {ε : ℝ} (hε : 0 < ε) :
    AEStronglyMeasurable (truncatedIntegral D.μ (ball Q.z Q.R) d.d' Q.cutoffKernel ε f)
      (D.μ.restrict (ball Q.z Q.R)) := by
  obtain ⟨M, hM, hb⟩ := Q.exists_truncated_kernel_bound hε
  have hfin : D.μ (ball Q.z Q.R) < ⊤ :=
    (measure_mono (Q.supported_localized_singular.sub_G.trans D.sub₁₂)).trans_lt D.finΩ₂
  have ht : ∀ x ∈ ball Q.z Q.R, ∀ y ∈ ball Q.z Q.R,
      |truncatedKernel d.d' Q.cutoffKernel ε x y| ≤ M := by
    intro x hx y hy
    by_cases he : ε < d.d' x y
    · simpa only [truncatedKernel, he, ite_true] using hb x hx y hy he
    · simpa only [truncatedKernel, he, ite_false, abs_zero] using hM
  have ha := bounded_kernel_action_aestronglyMeasurable isOpen_ball.measurableSet hfin
    (truncatedKernel_measurable d.meas Q.supported_localized_singular.kernel.measurable ε)
    hM ht (hf.measurable_subtype hδ) (ENNReal.toReal_nonneg (a := holderSup (ball Q.z Q.R) f))
    (fun _ hx => abs_le_holderSup hf.parts.1 hx)
  exact ha.congr (ae_of_all _ fun x => truncatedKernel_integral d.meas ε f x)

/-- Each positive truncation has the correct transposed adjoint.
Symmetry of the one fixed gauge is used precisely in the truncation region. -/
theorem TransposeData.truncated_adjoint {Q : LocalKernelData D d} (P : TransposeData Q)
    {δ : ℝ≥0} (hδ : 0 < δ) {f g : X → ℝ}
    (hf : BoundedHolder δ (ball Q.z Q.R) f) (hg : BoundedHolder δ (ball Q.z Q.R) g)
    {ε : ℝ} (hε : 0 < ε) :
    (∫ x in ball Q.z Q.R, truncatedIntegral D.μ (ball Q.z Q.R) d.d' Q.cutoffKernel ε f x * g x ∂D.μ) =
      ∫ x in ball Q.z Q.R, f x * truncatedIntegral D.μ (ball Q.z Q.R) d.d' P.data.cutoffKernel ε g x ∂D.μ := by
  obtain ⟨M, hM, hb⟩ := Q.exists_truncated_kernel_bound hε
  have hfin : D.μ (ball Q.z Q.R) < ⊤ :=
    (measure_mono (Q.supported_localized_singular.sub_G.trans D.sub₁₂)).trans_lt D.finΩ₂
  have ht : ∀ x ∈ ball Q.z Q.R, ∀ y ∈ ball Q.z Q.R,
      |truncatedKernel d.d' Q.cutoffKernel ε x y| ≤ M := by
    intro x hx y hy
    by_cases he : ε < d.d' x y
    · simpa only [truncatedKernel, he, ite_true] using hb x hx y hy he
    · simpa only [truncatedKernel, he, ite_false, abs_zero] using hM
  have he := bounded_kernel_adjoint isOpen_ball.measurableSet hfin
    (truncatedKernel_measurable d.meas Q.supported_localized_singular.kernel.measurable ε)
    hM ht (hf.measurable_subtype hδ) (hg.measurable_subtype hδ)
    (ENNReal.toReal_nonneg (a := holderSup (ball Q.z Q.R) f))
    (ENNReal.toReal_nonneg (a := holderSup (ball Q.z Q.R) g))
    (fun _ hx => abs_le_holderSup hf.parts.1 hx) (fun _ hx => abs_le_holderSup hg.parts.1 hx)
  simp only [truncatedKernel_integral d.meas] at he
  refine he.trans ?_
  apply integral_congr_ae
  exact ae_of_all _ fun y => by
    dsimp only
    congr 1
    have hh : (fun x => truncatedKernel d.d' Q.cutoffKernel ε x y * g x) =
        (fun x => truncatedKernel d.d' P.data.cutoffKernel ε y x * g x) := by
      funext x
      rw [truncatedKernel, truncatedKernel, P.cutoffKernel_eq y x, d.symm y x]
    rw [hh, truncatedKernel_integral d.meas]

end RothschildStein.H2

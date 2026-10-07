-- Copyright (c) 2026 Scott Armstrong and Amélie Loher. All rights reserved.
-- Released under Apache 2.0 license as described in the file LICENSE.
module
public import RothschildStein.H2.SingularL2OffDiagonal
public import RothschildStein.H2.LocalizedKernelMeasurable
public import RothschildStein.H2.LocalL2Certificate
@[expose] public section
set_option autoImplicit false
set_option relaxedAutoImplicit false
noncomputable section
open Set MeasureTheory Metric
open scoped ENNReal NNReal
namespace RothschildStein.H2
variable {X : Type*} [MetricSpace X] [MeasurableSpace X] [BorelSpace X]
variable {D : LocDoubling X} {d : TruncDist D}

/-- The actual Data D L² extension supplies the complete
analytic certificate of the Calderón–Zygmund and Lᵖ theorems. -/
theorem TransposeData.l2Certificate {Q : LocalKernelData D d} (P : TransposeData Q)
    {δ : ℝ≥0} (hδ : 0 < δ) (hδ₀ : (δ : ℝ) < Q.β₀) (hδβ : (δ : ℝ) < Q.β) (hδν : (δ : ℝ) < Q.ν)
    (hδ₀' : (δ : ℝ) < P.data.β₀) (hδβ' : (δ : ℝ) < P.data.β) (hδν' : (δ : ℝ) < P.data.ν) :
    LocalL2Certificate D Q.z Q.R (min P.data.β₀ P.data.β)
      P.data.singularA P.data.singularS (P.l2Constant δ) Q.cutoffKernel
      (P.l2Operator hδ hδ₀ hδβ hδν hδ₀' hδβ' hδν') where
  norm_le := (P.l2Operator_norm_bounds hδ hδ₀ hδβ hδν hδ₀' hδβ' hδν').1
  offDiagonal := P.l2Operator_offDiagonal hδ hδ₀ hδβ hδν hδ₀' hδβ' hδν'
  kernel_transpose := by
    have he : (fun x y => Q.cutoffKernel y x) = P.data.cutoffKernel :=
      funext fun x => funext fun y => (P.cutoffKernel_eq x y).symm
    rw [he]; exact P.data.localized_singular
  measurable_kernel := Q.cutoffKernel_measurable
  support := Q.cutoffKernel_outside

/-- The adjoint extension supplies the certificate with exchanged
kernel variables on the same L² space. -/
theorem TransposeData.transposeL2Certificate {Q : LocalKernelData D d} (P : TransposeData Q)
    {δ : ℝ≥0} (hδ : 0 < δ) (hδ₀ : (δ : ℝ) < Q.β₀) (hδβ : (δ : ℝ) < Q.β) (hδν : (δ : ℝ) < Q.ν)
    (hδ₀' : (δ : ℝ) < P.data.β₀) (hδβ' : (δ : ℝ) < P.data.β) (hδν' : (δ : ℝ) < P.data.ν) :
    LocalL2Certificate D Q.z Q.R (min Q.β₀ Q.β)
      Q.singularA Q.singularS (P.l2Constant δ) (fun x y => Q.cutoffKernel y x)
      (P.transposeL2Operator hδ hδ₀ hδβ hδν hδ₀' hδβ' hδν') where
  norm_le := (P.l2Operator_norm_bounds hδ hδ₀ hδβ hδν hδ₀' hδβ' hδν').2
  offDiagonal := by
    have he : P.data.cutoffKernel = fun x y => Q.cutoffKernel y x :=
      funext fun x => funext fun y => P.cutoffKernel_eq x y
    rw [← he]
    exact P.transposeL2Operator_offDiagonal hδ hδ₀ hδβ hδν hδ₀' hδβ' hδν'
  kernel_transpose := Q.localized_singular
  measurable_kernel := Q.cutoffKernel_measurable.comp measurable_swap
  support := by
    intro x y hxy
    exact Q.cutoffKernel_outside y x (hxy.elim Or.inr Or.inl)
end RothschildStein.H2

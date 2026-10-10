-- Copyright (c) 2026 Scott Armstrong and Amélie Loher. All rights reserved.
-- Released under Apache 2.0 license as described in the file LICENSE.
module

public import HeatKernel.Gaussian.SmoothKernelDerivative
public import RothschildStein.Definitions.sumSquares
import Mathlib.Tactic

/-! # Second horizontal derivatives of smooth kernel integrals

Joint second-order regularity supplies joint first-order regularity of a
horizontal kernel derivative. Two horizontal differentiations then commute
with integration against compact integrable data.
-/

@[expose] public section
set_option autoImplicit false
set_option relaxedAutoImplicit false
noncomputable section
open MeasureTheory Set RothschildStein Filter
open scoped Topology
namespace HeatKernel.Gaussian

/-- A joint second-order kernel and a first-order vector field give a jointly
first-order horizontal kernel derivative. -/
theorem contDiffOn_fieldDerivative_kernel {N : ℕ} {Z : Type*}
    [NormedAddCommGroup Z] [NormedSpace ℝ Z]
    {U : Set (Fin N → ℝ)} (hU : IsOpen U)
    (k : (Fin N → ℝ) × Z → ℝ) (hk : ContDiffOn ℝ 2 k (U ×ˢ univ))
    (V : (Fin N → ℝ) → (Fin N → ℝ)) (hV : ContDiffOn ℝ 1 V U) :
    ContDiffOn ℝ 1 (fun p : (Fin N → ℝ) × Z ↦
      fieldDerivative V (fun y ↦ k (y, p.2)) p.1) (U ×ˢ univ) := by
  have hk' : ContDiffOn ℝ 1 (fun p ↦
      (fderiv ℝ k p).comp (ContinuousLinearMap.inl ℝ (Fin N → ℝ) Z)) (U ×ˢ univ) :=
    (hk.fderiv_of_isOpen (hU.prod isOpen_univ) (by norm_num)).clm_comp contDiffOn_const
  have hV' : ContDiffOn ℝ 1 (fun p : (Fin N → ℝ) × Z ↦ V p.1) (U ×ˢ univ) :=
    hV.comp contDiffOn_fst (fun _ hp ↦ hp.1)
  apply (hk'.clm_apply hV').congr
  intro p hp
  have hd : DifferentiableAt ℝ k p := (hk.differentiableOn (by norm_num)).differentiableAt
    ((hU.prod isOpen_univ).mem_nhds hp)
  change fderiv ℝ (fun y ↦ k (y, p.2)) p.1 (V p.1) = _
  have hdp : HasFDerivAt (fun y ↦ k (y, p.2))
      ((fderiv ℝ k p).comp (ContinuousLinearMap.inl ℝ (Fin N → ℝ) Z)) p.1 :=
    hd.hasFDerivAt.comp p.1 (hasFDerivAt_prodMk_left p.1 p.2)
  rw [hdp.fderiv]

/-- Two horizontal differentiations commute with a compact-data integral under
joint second-order kernel regularity. -/
theorem fieldDerivative_fieldDerivative_kernel_integral_of_contDiff {N : ℕ} {Z : Type*}
    [NormedAddCommGroup Z] [NormedSpace ℝ Z] [MeasurableSpace Z]
    [BorelSpace Z] [SecondCountableTopology Z]
    (μ : Measure Z) {f : Z → ℝ} (hf : Integrable f μ)
    {K : Set Z} (hK : IsCompact K) (hsupp : Function.support f ⊆ K)
    {U : Set (Fin N → ℝ)} (hU : IsOpen U) {x : Fin N → ℝ} (hx : x ∈ U)
    (k : (Fin N → ℝ) × Z → ℝ) (hk : ContDiffOn ℝ 2 k (U ×ˢ univ))
    (V W : (Fin N → ℝ) → (Fin N → ℝ)) (hV : ContDiffOn ℝ 1 V U) :
    fieldDerivative W (fieldDerivative V (fun y ↦ ∫ z, f z * k (y, z) ∂μ)) x =
      ∫ z, f z * fieldDerivative W (fieldDerivative V (fun y ↦ k (y, z))) x ∂μ := by
  have heq : fieldDerivative V (fun y ↦ ∫ z, f z * k (y, z) ∂μ) =ᶠ[𝓝 x]
      fun y ↦ ∫ z, f z * fieldDerivative V (fun a ↦ k (a, z)) y ∂μ := by
    filter_upwards [hU.mem_nhds hx] with y hy
    exact fieldDerivative_kernel_integral_of_contDiff μ hf hK hsupp hU hy k
      (hk.of_le (by norm_num)) V
  change fderiv ℝ _ x (W x) = _
  rw [heq.fderiv_eq]
  exact fieldDerivative_kernel_integral_of_contDiff μ hf hK hsupp hU hx
    (fun p ↦ fieldDerivative V (fun y ↦ k (y, p.2)) p.1)
    (contDiffOn_fieldDerivative_kernel hU k hk V hV) W

/-- The second horizontal kernel derivative is integrable against compact data. -/
theorem integrable_second_fieldDerivative_kernel_of_contDiff {N : ℕ} {Z : Type*}
    [NormedAddCommGroup Z] [NormedSpace ℝ Z] [MeasurableSpace Z]
    [BorelSpace Z] [SecondCountableTopology Z]
    (μ : Measure Z) {f : Z → ℝ} (hf : Integrable f μ)
    {K : Set Z} (hK : IsCompact K) (hsupp : Function.support f ⊆ K)
    {U : Set (Fin N → ℝ)} (hU : IsOpen U) {x : Fin N → ℝ} (hx : x ∈ U)
    (k : (Fin N → ℝ) × Z → ℝ) (hk : ContDiffOn ℝ 2 k (U ×ˢ univ))
    (V W : (Fin N → ℝ) → (Fin N → ℝ)) (hV : ContDiffOn ℝ 1 V U) :
    Integrable (fun z ↦ f z * fieldDerivative W (fieldDerivative V (fun y ↦ k (y, z))) x) μ :=
  integrable_fderiv_kernel_apply_of_contDiff μ hf hK hsupp hU hx
    (fun p ↦ fieldDerivative V (fun y ↦ k (y, p.2)) p.1)
    (contDiffOn_fieldDerivative_kernel hU k hk V hV) (W x)

end HeatKernel.Gaussian

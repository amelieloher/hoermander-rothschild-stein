-- Copyright (c) 2026 Scott Armstrong and Amélie Loher. All rights reserved.
-- Released under Apache 2.0 license as described in the file LICENSE.
module

public import HeatKernel.Gaussian.CompactKernelDerivative
public import Mathlib.Analysis.Calculus.ContDiff.Comp
public import RothschildStein.Definitions.fieldDerivative
import Mathlib.Tactic

/-! # Kernel derivative interchange from joint regularity

Joint continuous differentiability supplies the continuous partial derivative
and local bounds required for compact-data derivative interchange.
-/

@[expose] public section
set_option autoImplicit false
set_option relaxedAutoImplicit false
noncomputable section
open MeasureTheory Set RothschildStein
namespace HeatKernel.Gaussian

/-- A jointly continuously differentiable kernel gives an integrable partial
derivative and the Fréchet derivative of its compact-data integral. -/
theorem hasFDerivAt_kernel_integral_of_contDiff {H Z E : Type*}
    [NormedAddCommGroup H] [NormedSpace ℝ H] [ProperSpace H]
    [NormedAddCommGroup Z] [NormedSpace ℝ Z] [MeasurableSpace Z]
    [BorelSpace Z] [SecondCountableTopology Z]
    [NormedAddCommGroup E] [NormedSpace ℝ E] [CompleteSpace E]
    (μ : Measure Z) {f : Z → ℝ} (hf : Integrable f μ)
    {K : Set Z} (hK : IsCompact K) (hsupp : Function.support f ⊆ K)
    {U : Set H} (hU : IsOpen U) {x : H} (hx : x ∈ U)
    (k : H × Z → E) (hk : ContDiffOn ℝ 1 k (U ×ˢ univ)) :
    Integrable (fun z ↦ f z • (fderiv ℝ k (x, z)).comp (ContinuousLinearMap.inl ℝ H Z)) μ ∧
      HasFDerivAt (fun y ↦ ∫ z, f z • k (y, z) ∂μ)
        (∫ z, f z • (fderiv ℝ k (x, z)).comp (ContinuousLinearMap.inl ℝ H Z) ∂μ) x := by
  apply hasFDerivAt_kernel_integral_of_compact_data μ hf hK hsupp hU hx k
    (fun p ↦ (fderiv ℝ k p).comp (ContinuousLinearMap.inl ℝ H Z)) hk.continuousOn
  · exact (hk.continuousOn_fderiv_of_isOpen (hU.prod isOpen_univ) le_rfl).clm_comp continuousOn_const
  · intro y hy z
    have hd : DifferentiableAt ℝ k (y, z) := (hk.differentiableOn (by norm_num)).differentiableAt
      ((hU.prod isOpen_univ).mem_nhds ⟨hy, mem_univ z⟩)
    exact hd.hasFDerivAt.comp y (hasFDerivAt_prodMk_left y z)

/-- Directional differentiation commutes with a compact-data kernel integral
under joint continuous differentiability alone. -/
theorem fderiv_kernel_integral_apply_of_contDiff {H Z E : Type*}
    [NormedAddCommGroup H] [NormedSpace ℝ H] [ProperSpace H]
    [NormedAddCommGroup Z] [NormedSpace ℝ Z] [MeasurableSpace Z]
    [BorelSpace Z] [SecondCountableTopology Z]
    [NormedAddCommGroup E] [NormedSpace ℝ E] [CompleteSpace E]
    (μ : Measure Z) {f : Z → ℝ} (hf : Integrable f μ)
    {K : Set Z} (hK : IsCompact K) (hsupp : Function.support f ⊆ K)
    {U : Set H} (hU : IsOpen U) {x : H} (hx : x ∈ U)
    (k : H × Z → E) (hk : ContDiffOn ℝ 1 k (U ×ˢ univ)) (v : H) :
    fderiv ℝ (fun y ↦ ∫ z, f z • k (y, z) ∂μ) x v =
      ∫ z, f z • fderiv ℝ (fun y ↦ k (y, z)) x v ∂μ := by
  obtain ⟨hi, hd⟩ := hasFDerivAt_kernel_integral_of_contDiff μ hf hK hsupp hU hx k hk
  rw [hd.fderiv, ContinuousLinearMap.integral_apply hi]
  apply integral_congr_ae
  apply Filter.Eventually.of_forall
  intro z
  have hdk : DifferentiableAt ℝ k (x, z) := (hk.differentiableOn (by norm_num)).differentiableAt
    ((hU.prod isOpen_univ).mem_nhds ⟨hx, mem_univ z⟩)
  have hdp : HasFDerivAt (fun y ↦ k (y, z))
      ((fderiv ℝ k (x, z)).comp (ContinuousLinearMap.inl ℝ H Z)) x :=
    hdk.hasFDerivAt.comp x (hasFDerivAt_prodMk_left x z)
  dsimp only
  rw [hdp.fderiv]
  rfl

/-- The directional derivative of a jointly continuously differentiable
kernel is integrable against compact integrable scalar data. -/
theorem integrable_fderiv_kernel_apply_of_contDiff {H Z E : Type*}
    [NormedAddCommGroup H] [NormedSpace ℝ H] [ProperSpace H]
    [NormedAddCommGroup Z] [NormedSpace ℝ Z] [MeasurableSpace Z]
    [BorelSpace Z] [SecondCountableTopology Z]
    [NormedAddCommGroup E] [NormedSpace ℝ E] [CompleteSpace E]
    (μ : Measure Z) {f : Z → ℝ} (hf : Integrable f μ)
    {K : Set Z} (hK : IsCompact K) (hsupp : Function.support f ⊆ K)
    {U : Set H} (hU : IsOpen U) {x : H} (hx : x ∈ U)
    (k : H × Z → E) (hk : ContDiffOn ℝ 1 k (U ×ˢ univ)) (v : H) :
    Integrable (fun z ↦ f z • fderiv ℝ (fun y ↦ k (y, z)) x v) μ := by
  have hi := (hasFDerivAt_kernel_integral_of_contDiff μ hf hK hsupp hU hx k hk).1
  apply ((ContinuousLinearMap.apply ℝ E v).integrable_comp hi).congr
  apply Filter.Eventually.of_forall
  intro z
  have hd : DifferentiableAt ℝ k (x, z) := (hk.differentiableOn (by norm_num)).differentiableAt
    ((hU.prod isOpen_univ).mem_nhds ⟨hx, mem_univ z⟩)
  have hdp : HasFDerivAt (fun y ↦ k (y, z))
      ((fderiv ℝ k (x, z)).comp (ContinuousLinearMap.inl ℝ H Z)) x :=
    hd.hasFDerivAt.comp x (hasFDerivAt_prodMk_left x z)
  dsimp only
  rw [hdp.fderiv]
  rfl

/-- Horizontal differentiation commutes with a compact-data kernel integral
whenever the kernel is jointly continuously differentiable. -/
theorem fieldDerivative_kernel_integral_of_contDiff {N : ℕ} {Z : Type*}
    [NormedAddCommGroup Z] [NormedSpace ℝ Z] [MeasurableSpace Z]
    [BorelSpace Z] [SecondCountableTopology Z]
    (μ : Measure Z) {f : Z → ℝ} (hf : Integrable f μ)
    {K : Set Z} (hK : IsCompact K) (hsupp : Function.support f ⊆ K)
    {U : Set (Fin N → ℝ)} (hU : IsOpen U) {x : Fin N → ℝ} (hx : x ∈ U)
    (k : (Fin N → ℝ) × Z → ℝ) (hk : ContDiffOn ℝ 1 k (U ×ˢ univ))
    (V : (Fin N → ℝ) → (Fin N → ℝ)) :
    fieldDerivative V (fun y ↦ ∫ z, f z * k (y, z) ∂μ) x =
      ∫ z, f z * fieldDerivative V (fun y ↦ k (y, z)) x ∂μ :=
  fderiv_kernel_integral_apply_of_contDiff μ hf hK hsupp hU hx k hk (V x)

end HeatKernel.Gaussian

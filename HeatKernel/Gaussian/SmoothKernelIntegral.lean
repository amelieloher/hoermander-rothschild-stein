-- Copyright (c) 2026 Scott Armstrong and Amélie Loher. All rights reserved.
-- Released under Apache 2.0 license as described in the file LICENSE.
module

public import HeatKernel.Gaussian.KernelIntegralContinuity
public import Mathlib.Analysis.Calculus.ContDiff.Comp
import Mathlib.Tactic

/-! # Smooth compact-data kernel evolutions

Induction on the derivative order passes joint kernel smoothness through
integration against compact integrable scalar data.
-/

@[expose] public section
set_option autoImplicit false
set_option relaxedAutoImplicit false
noncomputable section
open MeasureTheory Set Metric
open scoped ContDiff
universe u
namespace HeatKernel.Gaussian

/-- Finite joint smoothness of a kernel passes to its integral against compact
integrable data, including derivative-valued kernels. -/
theorem contDiffOn_kernel_integral_of_compact_data {H Z E : Type u}
    [NormedAddCommGroup H] [NormedSpace ℝ H] [ProperSpace H]
    [NormedAddCommGroup Z] [NormedSpace ℝ Z] [MeasurableSpace Z]
    [BorelSpace Z] [SecondCountableTopology Z]
    [NormedAddCommGroup E] [NormedSpace ℝ E] [CompleteSpace E]
    (μ : Measure Z) {f : Z → ℝ} (hf : Integrable f μ)
    {K : Set Z} (hK : IsCompact K) (hsupp : Function.support f ⊆ K)
    {U : Set H} (hU : IsOpen U) (n : ℕ) (k : H × Z → E)
    (hk : ContDiffOn ℝ n k (U ×ˢ univ)) :
    ContDiffOn ℝ n (fun x ↦ ∫ z, f z • k (x, z) ∂μ) U := by
  induction n generalizing E with
  | zero =>
    simpa only [WithTop.coe_natCast, Nat.cast_zero, contDiffOn_zero] using
      continuousOn_kernel_integral_of_compact_data μ hf hK hsupp hU k hk.continuousOn
  | succ n ih =>
    have hks : ContDiffOn ℝ ((n : ℕ∞ω) + 1) k (U ×ˢ univ) := by simpa using hk
    have hkn := (contDiffOn_succ_iff_fderiv_of_isOpen (hU.prod isOpen_univ)).mp hks
    let k' : H × Z → H →L[ℝ] E := fun a ↦
      (fderiv ℝ k a).comp (ContinuousLinearMap.inl ℝ H Z)
    have hk' : ContDiffOn ℝ n k' (U ×ˢ univ) :=
      hkn.2.2.clm_comp contDiffOn_const
    have hd : ∀ x ∈ U, HasFDerivAt (fun y ↦ ∫ z, f z • k (y, z) ∂μ)
        (∫ z, f z • k' (x, z) ∂μ) x := by
      intro x hx
      apply (hasFDerivAt_kernel_integral_of_compact_data μ hf hK hsupp hU hx k k'
        hk.continuousOn hk'.continuousOn ?_).2
      intro y hy z
      have H : HasFDerivAt k (fderiv ℝ k (y, z)) (y, z) :=
        (hkn.1.differentiableAt ((hU.prod isOpen_univ).mem_nhds ⟨hy, mem_univ z⟩)).hasFDerivAt
      exact H.comp y (hasFDerivAt_prodMk_left y z)
    have hresult : ContDiffOn ℝ ((n : ℕ∞ω) + 1) (fun x ↦ ∫ z, f z • k (x, z) ∂μ) U := by
      apply (contDiffOn_succ_iff_fderiv_of_isOpen hU).mpr
      refine ⟨fun x hx ↦ (hd x hx).differentiableAt.differentiableWithinAt, by simp, ?_⟩
      exact (ih k' hk').congr (fun x hx ↦ (hd x hx).fderiv)
    simpa using hresult

/-- Infinite joint smoothness of a kernel passes to its compact-data evolution. -/
theorem contDiffOn_infty_kernel_integral_of_compact_data {H Z E : Type u}
    [NormedAddCommGroup H] [NormedSpace ℝ H] [ProperSpace H]
    [NormedAddCommGroup Z] [NormedSpace ℝ Z] [MeasurableSpace Z]
    [BorelSpace Z] [SecondCountableTopology Z]
    [NormedAddCommGroup E] [NormedSpace ℝ E] [CompleteSpace E]
    (μ : Measure Z) {f : Z → ℝ} (hf : Integrable f μ)
    {K : Set Z} (hK : IsCompact K) (hsupp : Function.support f ⊆ K)
    {U : Set H} (hU : IsOpen U) (k : H × Z → E)
    (hk : ContDiffOn ℝ (⊤ : ℕ∞) k (U ×ˢ univ)) :
    ContDiffOn ℝ (⊤ : ℕ∞) (fun x ↦ ∫ z, f z • k (x, z) ∂μ) U := by
  apply contDiffOn_infty.mpr
  intro n
  exact contDiffOn_kernel_integral_of_compact_data μ hf hK hsupp hU n k
    (contDiffOn_infty.mp hk n)

end HeatKernel.Gaussian

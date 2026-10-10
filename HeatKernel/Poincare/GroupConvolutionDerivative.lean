-- Copyright (c) 2026 Scott Armstrong and Amélie Loher. All rights reserved.
-- Released under Apache 2.0 license as described in the file LICENSE.
module

public import HeatKernel.Poincare.WeightedFieldIntegral
public import RothschildStein.G2.ConvolutionSmooth

set_option autoImplicit false
set_option relaxedAutoImplicit false
@[expose] public section
noncomputable section
open Set Filter MeasureTheory RothschildStein
open scoped Topology
namespace HeatKernel

/-- Differentiation in the parameter of a group convolution acts on its smooth kernel,
even when its other factor is only locally integrable. -/
theorem fieldDerivative_groupConvolution_kernel {N : ℕ} (G : HomogeneousGroup N)
    {η f : (Fin N → ℝ) → ℝ} (hη : ContDiff ℝ (⊤ : ℕ∞) η)
    (hc : HasCompactSupport η) (hf : LocallyIntegrable f volume)
    (V : (Fin N → ℝ) → (Fin N → ℝ)) (x : Fin N → ℝ) :
    fieldDerivative V (G2.groupConvolution G η f) x =
      ∫ z, f z * fieldDerivative V (fun y => η (G.mul y (G.inv z))) x := by
  let Φ := fun p : (Fin N → ℝ) × (Fin N → ℝ) => η (G.mul p.1 (G.inv p.2))
  have hΦ : ContDiff ℝ 1 Φ :=
    (hη.comp ((G2.contDiff_mul G).comp
      (contDiff_fst.prodMk ((G2.contDiff_inv G).comp contDiff_snd)))).of_le (by simp)
  let K := Neg.neg '' G2.groupKernelSupport G η x
  have hK : IsCompact K := (G2.isCompact_groupKernelSupport G hc x).image continuous_neg
  have hv (y : Fin N → ℝ) (hy : y ∈ Metric.ball x 1) (z : Fin N → ℝ)
      (hz : z ∉ K) : Φ (y,z) = 0 := by
    have hn : -z ∉ G2.groupKernelSupport G η x := fun ht => hz ⟨-z, ht, neg_neg z⟩
    simpa only [G2.groupKernel, neg_neg] using G2.groupKernel_vanish G hy hn
  have he : G2.groupConvolution G η f =ᶠ[𝓝 x]
      (fun y => ∫ z in K, f z * Φ (y,z)) := by
    filter_upwards [Metric.ball_mem_nhds x zero_lt_one] with y hy
    rw [G2.groupConvolution_def]
    simp only [mul_comm (η _)]
    exact (setIntegral_eq_integral_of_forall_compl_eq_zero
      (fun z hz => by
        change f z * Φ (y,z) = 0
        rw [hv y hy z hz, mul_zero])).symm
  have hd := fieldDerivative_integral_weighted_compact_parameter hΦ hK
    (hf.integrableOn_isCompact hK) V x
  change fderiv ℝ (G2.groupConvolution G η f) x (V x) = _
  rw [he.fderiv_eq]
  change fieldDerivative V (fun y => ∫ z in K, f z * Φ (y,z)) x = _
  rw [hd]
  apply setIntegral_eq_integral_of_forall_compl_eq_zero
  intro z hz
  have hzero : HasFDerivAt (𝕜 := ℝ) (fun y => Φ (y,z)) 0 x :=
    hasFDerivAt_zero_of_eventually_const 0 (by
      filter_upwards [Metric.ball_mem_nhds x zero_lt_one] with y hy
      exact hv y hy z hz)
  change f z * fderiv ℝ (fun y => Φ (y,z)) x (V x) = 0
  rw [hzero.fderiv]
  simp only [zero_apply, mul_zero]

end HeatKernel

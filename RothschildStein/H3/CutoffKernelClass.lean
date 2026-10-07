-- Copyright (c) 2026 Scott Armstrong and Amélie Loher. All rights reserved.
-- Released under Apache 2.0 license as described in the file LICENSE.
module

public import RothschildStein.H3.CutoffKernelDifference
public import RothschildStein.H3.KernelWeightNormalization

set_option autoImplicit false
set_option relaxedAutoImplicit false
set_option backward.isDefEq.respectTransparency false
@[expose] public section
noncomputable section
namespace RothschildStein.H3
open Set Metric MeasureTheory
variable {N q : ℕ} {G : HomogeneousGroup N}

private theorem measurable_kernel_subtype {X : Type*} [MeasurableSpace X]
    {K : X → X → ℝ} (hK : Measurable (fun p : X × X => K p.1 p.2)) (E : Set X) :
    Measurable (fun p : E × E => K p.1 p.2) := by
  exact hK.comp ((measurable_subtype_coe.comp measurable_fst).prodMk
    (measurable_subtype_coe.comp measurable_snd))

private theorem normalized_kernel_smooth_factor {m ρ δ C Λ γ : ℝ}
    (hm : 0 < m) (hρ : 0 < ρ) :
    (m * C * Λ) * (ρ ^ γ / m) * (δ / ρ) = C * Λ * δ * ρ ^ (γ - 1) := by
  rw [Real.rpow_sub_one hρ.ne']
  field_simp [hm.ne', hρ.ne']

/-- The actual cutoff homogeneous kernel satisfies every shared H2 kernel
condition; its constants are linear in the actual first seminorm. -/
theorem cutoffGroupKernel_kernelClass_of_controlNorm
    {Y : Fin (q + 1) → (Fin N → ℝ) → (Fin N → ℝ)}
    (H : G2.ControlNormConclusion G driftWeight Y)
    (hY : ∀ i, ContinuousOn (Y i) {0}ᶜ)
    (hhomY : ∀ i, G2.IsHomogeneousField G (Y i) (if i = 0 then 2 else 1))
    {T χ : (Fin N → ℝ) → ℝ} (hT : ContDiffOn ℝ (⊤ : ℕ∞) T {0}ᶜ)
    {α : ℝ} (hα : 0 ≤ α) (hupper : α ≤ (G.homogeneousDimension : ℝ))
    (hhom : ∀ t : ℝ, 0 < t → ∀ x, x ≠ 0 →
      T (G.dilate t x) = t ^ (α - (G.homogeneousDimension : ℝ)) * T x)
    {R L : ℝ} (hR : 0 < R) (hL : 0 ≤ L) (hχmeas : Measurable χ)
    (hχ : ∀ z, 0 ≤ χ z ∧ χ z ≤ 1)
    (hχmod : ∀ a b, |χ a - χ b| ≤ L * G2.gaugeDistance G H.norm a b)
    (hsupp : ∀ z, R < H.norm z → χ z = 0) :
    let _metric := gaugeMetric G H.norm H.constant_one H.symmetric
    let m := (volume {z : Fin N → ℝ | H.norm z < 1}).toReal
    H2.KernelClass (volume : Measure (ControlCarrier N)) univ 1 α (m * kernelDerivativeBound H.norm T 1)
      (m * cutoffKernelSmoothConstant H.norm Y
        (α - (G.homogeneousDimension : ℝ)) R L * kernelDerivativeBound H.norm T 1)
      (fun x y : ControlCarrier N => cutoffGroupKernel G χ T x y) := by
  let _metric := gaugeMetric G H.norm H.constant_one H.symmetric
  let m := (volume {z : Fin N → ℝ | H.norm z < 1}).toReal
  let Λ := kernelDerivativeBound H.norm T 1
  let γ := α - (G.homogeneousDimension : ℝ)
  let C := cutoffKernelSmoothConstant H.norm Y γ R L
  have hm : 0 < m := gauge_unit_volume_toReal_pos G H.norm
  have hΛ : 0 ≤ Λ := (kernelDerivativeBound_properties H.norm.gauge hT 1).1
  have hC : 0 ≤ C := cutoffKernelSmoothConstant_nonneg H.norm Y γ hR.le hL
  have hγ : γ ≤ 0 := sub_nonpos.mpr hupper
  have hSphere : kernelSphereBound H.norm T ≤ Λ := by
    rw [← kernelDerivativeBound_zero H.norm T]
    exact kernelDerivativeBound_mono H.norm T (by omega)
  have hfull : Measurable (fun p : ControlCarrier N × ControlCarrier N =>
      cutoffGroupKernel G χ T p.1 p.2) := by
    simpa only [ControlCarrier, controlCarrierMeasureSpace] using
      cutoffGroupKernel_measurable G hχmeas hT.continuousOn
  change H2.KernelClass (volume : Measure (ControlCarrier N)) univ 1 α (m * Λ)
    (m * C * Λ) (fun x y : ControlCarrier N => cutoffGroupKernel G χ T x y)
  refine ⟨MeasurableSet.univ,
    ?_,
    by norm_num, le_refl 1, hα, mul_nonneg hm.le hΛ,
    mul_nonneg (mul_nonneg hm.le hC) hΛ, ?_, ?_⟩
  · exact measurable_kernel_subtype hfull univ
  · intro x hx y hy hxy
    have hb := truncatedKernel_h2_size G H.norm H.constant_one H.symmetric
      hT.continuousOn hhom (le_refl α) hR hχ hsupp x y hxy
    simp only [sub_self, Real.rpow_zero, mul_one] at hb
    exact hb.trans (mul_le_mul_of_nonneg_right
      (mul_le_mul_of_nonneg_left hSphere hm.le) (H2.kernelWeight_nonneg (volume : Measure (ControlCarrier N)) α x y))
  · intro x₀ hx₀ x hx y hy hsep
    have hρ : 0 < dist x₀ y := by linarith [dist_nonneg (x := x₀) (y := x)]
    have hxy : x₀ ≠ y := dist_pos.mp hρ
    have hb := cutoffGroupKernel_difference_of_controlNorm H hY hhomY hT hγ hhom
      hR hL hχ hχmod hsupp x₀ x y hsep
    rw [kernelWeight_gauge_eq G H.norm H.constant_one H.symmetric α x₀ y hxy,
      Real.rpow_one]
    have he := normalized_kernel_smooth_factor (C := C) (Λ := Λ) (γ := γ)
      (δ := dist x₀ x) hm hρ
    exact hb.trans_eq he.symm

end RothschildStein.H3

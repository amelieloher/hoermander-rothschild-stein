-- Copyright (c) 2026 Scott Armstrong and Amélie Loher. All rights reserved.
-- Released under Apache 2.0 license as described in the file LICENSE.
module

public import RothschildStein.H3.CutoffKernelFullClass
public import RothschildStein.H3.KernelWeightNormalization
public import RothschildStein.H3.CutoffKernelGeometryConstant
public import RothschildStein.H3.KernelBounds

set_option autoImplicit false
set_option relaxedAutoImplicit false
set_option backward.isDefEq.respectTransparency false
@[expose] public section
noncomputable section
namespace RothschildStein.H3
open Set Metric MeasureTheory
variable {N q : ℕ} {G : HomogeneousGroup N}

/-- The actual cutoff homogeneous kernel satisfies every shared H2 kernel
condition; its constants are linear in the actual first seminorm. -/
theorem cutoffGroupKernel_kernelClass_uniform_of_controlNorm
    {Y : Fin (q + 1) → (Fin N → ℝ) → (Fin N → ℝ)}
    (H : G2.ControlNormConclusion G driftWeight Y)
    (hY : ∀ i, ContinuousOn (Y i) {0}ᶜ)
    (hhomY : ∀ i, G2.IsHomogeneousField G (Y i) (if i = 0 then 2 else 1))
    {T χ : (Fin N → ℝ) → ℝ} (hT : ContDiffOn ℝ (⊤ : ℕ∞) T {0}ᶜ)
    {v α : ℝ} (hv : 0 ≤ v) (hvα : v ≤ α)
    (hupper : α < (G.homogeneousDimension : ℝ))
    (hhom : ∀ t : ℝ, 0 < t → ∀ x, x ≠ 0 →
      T (G.dilate t x) = t ^ (α - (G.homogeneousDimension : ℝ)) * T x)
    {R L : ℝ} (hR : 0 < R) (hL : 0 ≤ L) (hχmeas : Measurable χ)
    (hχ : ∀ z, 0 ≤ χ z ∧ χ z ≤ 1)
    (hχmod : ∀ a b, |χ a - χ b| ≤ L * G2.gaugeDistance G H.norm a b)
    (hsupp : ∀ z, R < H.norm z → χ z = 0) :
    let _metric := gaugeMetric G H.norm H.constant_one H.symmetric
    let m := (volume {z : Fin N → ℝ | H.norm z < 1}).toReal
    H2.KernelClass volume univ 1 v (m * kernelSphereBound H.norm T * R ^ (α - v))
      (m * cutoffKernelFrameConstant H.norm Y (G.homogeneousDimension : ℝ) *
        (1 + R * L) * kernelDerivativeBound H.norm T 1 * (2 : ℝ) ^ (G.homogeneousDimension : ℝ) * R ^ (α - v))
      (fun x y : ControlCarrier N => cutoffGroupKernel G χ T x y) := by
  let _metric := gaugeMetric G H.norm H.constant_one H.symmetric
  have Hv := cutoffGroupKernel_kernelClass_lower_order_of_controlNorm H hY hhomY hT
    hv hvα hupper hhom hR hL hχmeas hχ hχmod hsupp
  apply kernelClass_mono_constants Hv (le_refl _)
  have hC := cutoffKernelSmoothConstant_le_frame H.norm Y
    (Q := (G.homogeneousDimension : ℝ))
    (γ := α - (G.homogeneousDimension : ℝ)) (by linarith) hR.le hL
  have hp : (2 : ℝ) ^ (α - v) ≤ (2 : ℝ) ^ (G.homogeneousDimension : ℝ) :=
    Real.rpow_le_rpow_of_exponent_le (by norm_num) (by linarith)
  have hm : 0 ≤ (volume {z : Fin N → ℝ | H.norm z < 1}).toReal := ENNReal.toReal_nonneg
  have hΛ := (kernelDerivativeBound_properties H.norm.gauge hT 1).1
  have hRpow : 0 ≤ R ^ (α - v) := Real.rpow_nonneg hR.le _
  have hCp : 0 ≤ cutoffKernelFrameConstant H.norm Y (G.homogeneousDimension : ℝ) *
      (1 + R * L) := mul_nonneg
    (cutoffKernelFrameConstant_pos H.norm Y _).le (by positivity)
  have hb := mul_le_mul_of_nonneg_right
    (mul_le_mul
      (mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_left hC hm) hΛ)
      hp (Real.rpow_nonneg (by norm_num) _) (mul_nonneg (mul_nonneg hm hCp) hΛ)) hRpow
  simpa only [mul_assoc] using hb

end RothschildStein.H3

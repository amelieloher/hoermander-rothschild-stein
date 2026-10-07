-- Copyright (c) 2026 Scott Armstrong and Amélie Loher. All rights reserved.
-- Released under Apache 2.0 license as described in the file LICENSE.
module

public import RothschildStein.H3.CutoffKernelClass
public import RothschildStein.H3.KernelWeightNormalization
public import RothschildStein.H3.CutoffKernelLowerOrder

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
theorem cutoffGroupKernel_kernelClass_lower_order_of_controlNorm
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
      (m * cutoffKernelSmoothConstant H.norm Y
        (α - (G.homogeneousDimension : ℝ)) R L * kernelDerivativeBound H.norm T 1 * (2 : ℝ) ^ (α - v) * R ^ (α - v))
      (fun x y : ControlCarrier N => cutoffGroupKernel G χ T x y) := by
  let _metric := gaugeMetric G H.norm H.constant_one H.symmetric
  have Hα := cutoffGroupKernel_kernelClass_of_controlNorm H hY hhomY hT
    (hv.trans hvα) hupper.le hhom hR hL hχmeas hχ hχmod hsupp
  have Hv := kernelClass_lower_order_of_support Hα hv hvα hR
    (fun x y hr => cutoffGroupKernel_eq_zero (G := G) hsupp x y hr)
  dsimp only at Hv ⊢
  rw [Real.mul_rpow (by norm_num : (0 : ℝ) ≤ 2) hR.le] at Hv
  have hs : 0 ≤ kernelSphereBound H.norm T := (kernelSphereBound_continuous H.norm.gauge hT.continuousOn).1
  refine ⟨Hv.measurable_E, Hv.measurable, Hv.β_pos, Hv.β_le_one, hv,
    mul_nonneg (mul_nonneg ENNReal.toReal_nonneg hs) (Real.rpow_nonneg hR.le _),
    ?_, ?_, ?_⟩
  · convert Hv.S_nonneg using 1; ring
  · intro x hx y hy hxy
    exact truncatedKernel_h2_size G H.norm H.constant_one H.symmetric
      hT.continuousOn hhom hvα hR hχ hsupp x y hxy
  · intro x₀ hx₀ x hx y hy hsep
    convert Hv.smooth x₀ hx₀ x hx y hy hsep using 1; ring

end RothschildStein.H3

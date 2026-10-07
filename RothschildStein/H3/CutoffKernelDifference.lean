-- Copyright (c) 2026 Scott Armstrong and Amélie Loher. All rights reserved.
-- Released under Apache 2.0 license as described in the file LICENSE.
module

public import RothschildStein.H3.CutoffKernelFarSmoothness
public import RothschildStein.H3.KernelNearSmoothness
public import RothschildStein.H3.ControlMetric

set_option autoImplicit false
set_option relaxedAutoImplicit false
set_option backward.isDefEq.respectTransparency false
@[expose] public section
noncomputable section
namespace RothschildStein.H3
open Set Metric
variable {N q : ℕ} {G : HomogeneousGroup N}

/-- The cutoff smoothness coefficient depends on the frame, degree and cutoff. -/
def cutoffKernelSmoothConstant (ν : (Fin N → ℝ) → ℝ)
    (Y : Fin (q + 1) → (Fin N → ℝ) → (Fin N → ℝ)) (γ R L : ℝ) : ℝ :=
  ((2 : ℝ) ^ (2 - γ) * max 0 (frameCoefficientSphereBound ν Y) +
    (2 : ℝ) ^ (-γ) * (2 * R * L)) + 4 * (1 + (2 : ℝ) ^ (-γ))

/-- The smoothness coefficient is nonnegative for every allowed cutoff. -/
theorem cutoffKernelSmoothConstant_nonneg (ν : (Fin N → ℝ) → ℝ)
    (Y : Fin (q + 1) → (Fin N → ℝ) → (Fin N → ℝ)) (γ : ℝ)
    {R L : ℝ} (hR : 0 ≤ R) (hL : 0 ≤ L) :
    0 ≤ cutoffKernelSmoothConstant ν Y γ R L := by
  unfold cutoffKernelSmoothConstant
  positivity

/-- Cases I and II give the complete exponent-one cutoff difference estimate. -/
theorem cutoffGroupKernel_difference_of_controlNorm
    {Y : Fin (q + 1) → (Fin N → ℝ) → (Fin N → ℝ)}
    (H : G2.ControlNormConclusion G driftWeight Y)
    (hY : ∀ i, ContinuousOn (Y i) {0}ᶜ)
    (hhomY : ∀ i, G2.IsHomogeneousField G (Y i) (if i = 0 then 2 else 1))
    {T χ : (Fin N → ℝ) → ℝ} (hT : ContDiffOn ℝ (⊤ : ℕ∞) T {0}ᶜ)
    {γ : ℝ} (hγ : γ ≤ 0)
    (hhom : ∀ t : ℝ, 0 < t → ∀ x, x ≠ 0 → T (G.dilate t x) = t ^ γ * T x)
    {R L : ℝ} (hR : 0 < R) (hL : 0 ≤ L)
    (hχ : ∀ z, 0 ≤ χ z ∧ χ z ≤ 1)
    (hχmod : ∀ a b, |χ a - χ b| ≤ L * G2.gaugeDistance G H.norm a b)
    (hsupp : ∀ z, R < H.norm z → χ z = 0) :
    let _metric := gaugeMetric G H.norm H.constant_one H.symmetric
    ∀ x₀ x y : ControlCarrier N, 2 * dist x₀ x < dist x₀ y →
      |cutoffGroupKernel G χ T x₀ y - cutoffGroupKernel G χ T x y| ≤
        cutoffKernelSmoothConstant H.norm Y γ R L * kernelDerivativeBound H.norm T 1 *
          dist x₀ x * dist x₀ y ^ (γ - 1) := by
  let _metric := gaugeMetric G H.norm H.constant_one H.symmetric
  let Λ := kernelDerivativeBound H.norm T 1
  let CF := (2 : ℝ) ^ (2 - γ) * max 0 (frameCoefficientSphereBound H.norm Y) +
    (2 : ℝ) ^ (-γ) * (2 * R * L)
  let CN := 4 * (1 + (2 : ℝ) ^ (-γ))
  have hΛ : 0 ≤ Λ := (kernelDerivativeBound_properties H.norm.gauge hT 1).1
  have hCF : 0 ≤ CF := by dsimp only [CF]; positivity
  have hCN : 0 ≤ CN := by dsimp only [CN]; positivity
  have hSphere : kernelSphereBound H.norm T ≤ Λ := by
    rw [← kernelDerivativeBound_zero H.norm T]
    exact kernelDerivativeBound_mono H.norm T (by omega)
  have hsize : ∀ a b : ControlCarrier N, a ≠ b →
      |cutoffGroupKernel G χ T a b| ≤ Λ * dist a b ^ γ := by
    intro a b hab
    have hz : G.mul (G.inv b) a ≠ 0 := by
      intro hz
      apply hab
      apply (G2.gaugeDistance_eq_zero_iff G H.norm.gauge a b).mp
      change H.norm (G.mul (G.inv b) a) = 0
      rw [hz, (H.norm.gauge.2.2.1 0).mpr rfl]
    have hb := kernelSphereBound_homogeneous H.norm.gauge hT.continuousOn hhom _ hz
    unfold cutoffGroupKernel
    rw [abs_mul, abs_of_nonneg (hχ _).1]
    calc
      _ ≤ 1 * |T (G.mul (G.inv b) a)| :=
        mul_le_mul_of_nonneg_right (hχ _).2 (abs_nonneg _)
      _ ≤ kernelSphereBound H.norm T * H.norm (G.mul (G.inv b) a) ^ γ :=
        by simpa only [one_mul] using hb
      _ ≤ Λ * dist a b ^ γ := mul_le_mul_of_nonneg_right hSphere
        (Real.rpow_nonneg (H.norm.gauge.2.1 _) _)
  dsimp only
  intro x₀ x y hsep
  by_cases hne : x₀ = x
  · subst x
    simp only [sub_self, abs_zero, dist_self, mul_zero, zero_mul, le_refl]
  have hp : 0 ≤ Λ * dist x₀ x * dist x₀ y ^ (γ - 1) := by positivity
  change _ ≤ (CF + CN) * Λ * dist x₀ x * dist x₀ y ^ (γ - 1)
  by_cases hfar : 4 * dist x₀ x ≤ dist x₀ y
  · have hf := cutoffGroupKernel_far_difference_of_controlNorm H hY hhomY hT hγ hhom
      hR hL hχ hχmod hsupp hne hfar
    calc
      _ ≤ CF * (Λ * dist x₀ x * dist x₀ y ^ (γ - 1)) := hf.trans_eq (by change CF * Λ * dist x₀ x * dist x₀ y ^ (γ - 1) = _; ring)
      _ ≤ (CF + CN) * (Λ * dist x₀ x * dist x₀ y ^ (γ - 1)) :=
        mul_le_mul_of_nonneg_right (le_add_of_nonneg_right hCN) hp
      _ = _ := by ring
  · have hn := kernel_difference_near_of_size hΛ hγ hsize hsep (lt_of_not_ge hfar).le
    calc
      _ ≤ (4 * Λ * (1 + (2 : ℝ) ^ (-γ))) * dist x₀ x * dist x₀ y ^ (γ - 1) := hn
      _ = CN * (Λ * dist x₀ x * dist x₀ y ^ (γ - 1)) := by ring
      _ ≤ (CF + CN) * (Λ * dist x₀ x * dist x₀ y ^ (γ - 1)) :=
        mul_le_mul_of_nonneg_right (le_add_of_nonneg_left hCF) hp
      _ = _ := by ring

end RothschildStein.H3

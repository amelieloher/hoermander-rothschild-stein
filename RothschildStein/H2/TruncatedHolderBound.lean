-- Copyright (c) 2026 Scott Armstrong and Amélie Loher. All rights reserved.
-- Released under Apache 2.0 license as described in the file LICENSE.
module

public import RothschildStein.H2.SingularHolder
public import RothschildStein.H2.IntegralSubsetBounds

@[expose] public section
set_option autoImplicit false
set_option relaxedAutoImplicit false
noncomputable section
open Set MeasureTheory Metric
open scoped NNReal ENNReal

namespace RothschildStein.H2
variable {X : Type*} [MetricSpace X] [MeasurableSpace X] [BorelSpace X]
variable {D : LocDoubling X} {d : TruncDist D}

/-- The positive truncation is the truncated regularized integral
plus its truncated T(1) term. Both summands are integrable. -/
theorem LocalKernelData.truncated_eq_regularized (Q : LocalKernelData D d) {δ : ℝ≥0}
    (hδ : 0 < δ) {f : X → ℝ} (hf : BoundedHolder δ (ball Q.z Q.R) f)
    {ε : ℝ} (hε : 0 < ε) {x : X} (hx : x ∈ ball Q.z Q.R) :
    truncatedIntegral D.μ (ball Q.z Q.R) d.d' Q.cutoffKernel ε f x =
      (∫ y in ball Q.z Q.R ∩ {y | ε < d.d' x y},
        Q.cutoffKernel x y * (f y - f x) ∂D.μ) +
      truncatedIntegral D.μ (ball Q.z Q.R) d.d' Q.cutoffKernel ε (fun _ => 1) x * f x := by
  have hi := Q.supported_localized_singular.regularized_absolute hδ hf hx
  have hir := hi.1.mono_set (inter_subset_left : ball Q.z Q.R ∩ {y | ε < d.d' x y} ⊆ _)
  have hj := (Q.supported_localized_singular.truncated_absolute d hε
    (f := fun _ => 1) aestronglyMeasurable_const (M := 1) (by norm_num)
    (ae_of_all _ (by intro y; norm_num)) hx).1
  unfold truncatedIntegral
  simp only [mul_one]
  rw [← integral_mul_const, ← integral_add hir (by simpa only [mul_one] using hj.mul_const (f x))]
  apply integral_congr_ae
  exact ae_of_all _ fun y => by ring

/-- Uniform domination of every positive truncated PV action.
The constant is independent of ε and uses the stated kernel and truncation bounds. -/
theorem LocalKernelData.truncated_abs_le (Q : LocalKernelData D d) {δ : ℝ≥0}
    (hδ : 0 < δ) {f : X → ℝ} (hf : BoundedHolder δ (ball Q.z Q.R) f)
    {ε : ℝ} (hε : 0 < ε) {x : X} (hx : x ∈ ball Q.z Q.R) :
    |truncatedIntegral D.μ (ball Q.z Q.R) d.d' Q.cutoffKernel ε f x| ≤
      Q.singularA * (holderSemi δ (ball Q.z Q.R) f).toReal *
        volumeIntegralConstant D.C_D δ * (2 * Q.R) ^ (δ : ℝ) +
      Q.cancellationConstant * (holderSup (ball Q.z Q.R) f).toReal := by
  have hi := Q.supported_localized_singular.regularized_absolute hδ hf hx
  simp only [zero_add] at hi
  have hA := Q.localized_singular.A_nonneg
  have hC := (volumeIntegralConstant_pos (C := D.C_D) (by linarith [D.one_lt_C_D]) hδ).le
  have hc : 0 ≤ Q.singularA * (holderSemi δ (ball Q.z Q.R) f).toReal *
      volumeIntegralConstant D.C_D δ * (2 * Q.R) ^ (δ : ℝ) := by
    exact mul_nonneg (mul_nonneg (mul_nonneg hA ENNReal.toReal_nonneg) hC)
      (Real.rpow_nonneg (by linarith [Q.radius_pos]) _)
  have hb := abs_setIntegral_le_of_subset (H := ball Q.z Q.R ∩ {y | ε < d.d' x y}) hi.1 inter_subset_left hc hi.2
  rw [Q.truncated_eq_regularized hδ hf hε hx]
  refine (abs_add_le _ _).trans (add_le_add hb ?_)
  rw [abs_mul]
  exact mul_le_mul (Q.truncated_one_bound hx hε)
    (abs_le_holderSup hf.parts.1 hx) (abs_nonneg _) Q.cancellationConstant_nonneg

end RothschildStein.H2

-- Copyright (c) 2026 Scott Armstrong and Amélie Loher. All rights reserved.
-- Released under Apache 2.0 license as described in the file LICENSE.
module

public import RothschildStein.H2.SplittingDominants

set_option autoImplicit false
set_option relaxedAutoImplicit false

@[expose] public section
noncomputable section
open Set MeasureTheory Metric Filter
open scoped NNReal ENNReal Topology

namespace RothschildStein.H2
variable {X : Type*} [MetricSpace X] [MeasurableSpace X] [BorelSpace X]
variable {D : LocDoubling X} {d : TruncDist D}

/-- (3) Subtracting b(x) is legitimate on any input region separated
from the diagonal where the singular piece has zero integral. BB p. 307. -/
theorem LocalKernelData.localized_integral_split_of_zero (Q : LocalKernelData D d)
    {x : X} (hx : x ∈ ball Q.z Q.R) {S : Set X} (hS : MeasurableSet S)
    {r : ℝ} (hr : 0 < r) (hSr : ∀ y ∈ S, r < d.d' x y)
    (hz : (∫ y in ball Q.z (2 * Q.R) ∩ S, Q.K₀ x y ∂D.μ) = 0) :
    (∫ y in ball Q.z Q.R ∩ S, Q.cutoffKernel x y ∂D.μ) =
      Q.a x * ((∫ y in ball Q.z (2 * Q.R) ∩ S, Q.K₀ x y * (Q.b y - Q.b x) ∂D.μ) +
        ∫ y in ball Q.z (2 * Q.R) ∩ S, Q.K₁ x y * Q.b y ∂D.μ) := by
  have hsub : ball Q.z (2 * Q.R) ∩ S ⊆ ball Q.z (2 * Q.R) ∩ {y | r < d.d' x y} :=
    fun y hy => ⟨hy.1, hSr y hy.2⟩
  have hk' := (Q.supported_singular.truncated_absolute d hr (f := fun _ => 1)
    aestronglyMeasurable_const (M := 1) (by norm_num) (ae_of_all _ (by intro y; norm_num)) hx).1
  have hk : IntegrableOn (Q.K₀ x) (ball Q.z (2 * Q.R) ∩ S) D.μ := by
    simpa only [mul_one] using hk'.mono_set hsub
  have hir : IntegrableOn (fun y => Q.K₀ x y * (Q.b y - Q.b x)) (ball Q.z (2 * Q.R) ∩ S) D.μ :=
    (Q.singular_b_absolute hx).1.mono_set inter_subset_left
  have hi₁ : IntegrableOn (fun y => Q.K₁ x y * Q.b y) (ball Q.z (2 * Q.R) ∩ S) D.μ :=
    (Q.fractional_b_absolute hx).1.mono_set inter_subset_left
  have he : (fun y => Q.sumKernel x y * Q.b y) =
      (fun y => (Q.K₀ x y * (Q.b y - Q.b x) + Q.K₀ x y * Q.b x) + Q.K₁ x y * Q.b y) := by
    funext y
    unfold LocalKernelData.sumKernel
    ring
  have hic : IntegrableOn (fun y => Q.K₀ x y * Q.b x) (ball Q.z (2 * Q.R) ∩ S) D.μ := hk.mul_const (Q.b x)
  have hsum : IntegrableOn (fun y => Q.K₀ x y * (Q.b y - Q.b x) + Q.K₀ x y * Q.b x)
      (ball Q.z (2 * Q.R) ∩ S) D.μ := hir.add hic
  unfold LocalKernelData.cutoffKernel
  rw [Q.localized_integral_eq hx hS, he, integral_add hsum hi₁,
    integral_add hir hic, integral_mul_const, hz, zero_mul, add_zero]

/-- (3) The same two absolute dominants control every zero-mean
input region, independently of the truncation radius. -/
theorem LocalKernelData.localized_integral_bound_of_zero (Q : LocalKernelData D d)
    {x : X} (hx : x ∈ ball Q.z Q.R) {S : Set X} (hS : MeasurableSet S)
    {r : ℝ} (hr : 0 < r) (hSr : ∀ y ∈ S, r < d.d' x y)
    (hz : (∫ y in ball Q.z (2 * Q.R) ∩ S, Q.K₀ x y ∂D.μ) = 0) :
    |∫ y in ball Q.z Q.R ∩ S, Q.cutoffKernel x y ∂D.μ| ≤ Q.cancellationConstant := by
  rw [Q.localized_integral_split_of_zero hx hS hr hSr hz, abs_mul,
    abs_of_nonneg (Q.cutoff_a.nonneg x)]
  obtain ⟨hir, hbr⟩ := Q.singular_b_absolute hx
  obtain ⟨hi₁, hb₁⟩ := Q.fractional_b_absolute hx
  have hCD : 0 ≤ D.C_D := by linarith [D.one_lt_C_D]
  have hc₀ : 0 ≤ 2 * D.C_D * Q.R * (Q.Lᵦ : ℝ) * Q.A₀ := by
    have := Q.singular.A_nonneg
    have := Q.radius_pos.le
    positivity
  have hc₁ : 0 ≤ Q.A₁ * volumeIntegralConstant D.C_D Q.ν * Q.R ^ Q.ν :=
    mul_nonneg (mul_nonneg Q.fractional.A_nonneg
      (volumeIntegralConstant_pos (C := D.C_D) (by linarith [D.one_lt_C_D]) Q.ν_pos).le)
      (Real.rpow_nonneg Q.radius_pos.le _)
  have he₀ := abs_setIntegral_le_of_subset hir (H := ball Q.z (2 * Q.R) ∩ S) inter_subset_left hc₀ hbr
  have he₁ := abs_setIntegral_le_of_subset hi₁ (H := ball Q.z (2 * Q.R) ∩ S) inter_subset_left hc₁ hb₁
  have he₂ := abs_add_le (∫ y in ball Q.z (2 * Q.R) ∩ S, Q.K₀ x y * (Q.b y - Q.b x) ∂D.μ)
    (∫ y in ball Q.z (2 * Q.R) ∩ S, Q.K₁ x y * Q.b y ∂D.μ)
  have he₃ := mul_le_mul_of_nonneg_right (Q.cutoff_a.le_one x)
    (abs_nonneg ((∫ y in ball Q.z (2 * Q.R) ∩ S, Q.K₀ x y * (Q.b y - Q.b x) ∂D.μ) +
      ∫ y in ball Q.z (2 * Q.R) ∩ S, Q.K₁ x y * Q.b y ∂D.μ))
  unfold LocalKernelData.cancellationConstant
  linarith

/-- Exact open-shell cancellation for the localized kernel,
BB Proposition 7.17, p. 307; the data include the support and cancellation hypotheses. -/
theorem LocalKernelData.shellCancellation (Q : LocalKernelData D d) :
    ShellCancellation D.μ (ball Q.z Q.R) (ball Q.z Q.R) d.d' Q.cutoffKernel Q.cancellationConstant := by
  refine ⟨Q.cancellationConstant_nonneg, ?_⟩
  intro x hx r₁ r₂ h₁ h₁₂
  have hm : Measurable (d.d' x) := d.meas.comp (measurable_const.prodMk measurable_id)
  exact Q.localized_integral_bound_of_zero hx
    ((measurableSet_lt measurable_const hm).inter (measurableSet_lt hm measurable_const))
    h₁ (fun y hy => hy.1) (Q.vanishing_all hx h₁ h₁₂)

/-- Uniform truncated T(1) bound, BB p. 307. -/
theorem LocalKernelData.truncated_one_bound (Q : LocalKernelData D d) {x : X}
    (hx : x ∈ ball Q.z Q.R) {ε : ℝ} (hε : 0 < ε) :
    |truncatedIntegral D.μ (ball Q.z Q.R) d.d' Q.cutoffKernel ε (fun _ => 1) x| ≤ Q.cancellationConstant := by
  have hm : Measurable (d.d' x) := d.meas.comp (measurable_const.prodMk measurable_id)
  have hz := Q.truncated_singular_one_eq_zero hx hε
  simp only [truncatedIntegral, mul_one] at hz ⊢
  exact Q.localized_integral_bound_of_zero hx (measurableSet_lt measurable_const hm)
    hε (fun y hy => hy) hz

end RothschildStein.H2

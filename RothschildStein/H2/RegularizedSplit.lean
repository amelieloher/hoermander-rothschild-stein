-- Copyright (c) 2026 Scott Armstrong and Amélie Loher. All rights reserved.
-- Released under Apache 2.0 license as described in the file LICENSE.
module

public import RothschildStein.H2.RegularizedFarDifference

set_option autoImplicit false
set_option relaxedAutoImplicit false

@[expose] public section
noncomputable section
open Set MeasureTheory Metric
open scoped ENNReal NNReal

namespace RothschildStein.H2
variable {X : Type*} [MetricSpace X] [MeasurableSpace X] [BorelSpace X]

/-- Strict far and closed near splitting for the regularized singular
integral. BB pp. 303–304, with the shell endpoint corrections. -/
theorem SupportedKernel.regularized_small_difference {D : LocDoubling X} {E G : Set X}
    {β A S R C_K : ℝ} {K : X → X → ℝ} (hK : SupportedKernel D E G β 0 A S R K)
    (d : TruncDist D) (hCan : ShellCancellation D.μ E G d.d' K C_K)
    {δ : ℝ≥0} (hδ : 0 < δ) (hδβ : (δ : ℝ) < β) {f : X → ℝ} (hf : BoundedHolder δ G f)
    {x₀ x : X} (hx₀ : x₀ ∈ E) (hx : x ∈ E) (hxx : x₀ ≠ x)
    (hκ : dist x₀ x < D.κ / 3) :
    |regularizedIntegral D.μ G K f x - regularizedIntegral D.μ G K f x₀| ≤
      (volumeIntegralConstant D.C_D (β - δ) * S + C_K +
        cancellationBoundaryConstant D.C_D d.θ₁ d.θ₂ * A) *
          (holderSemi δ G f).toReal * dist x₀ x ^ (δ : ℝ) +
      A * (holderSemi δ G f).toReal * volumeIntegralConstant D.C_D δ * (3 * dist x₀ x) ^ (δ : ℝ) +
      A * (holderSemi δ G f).toReal * volumeIntegralConstant D.C_D δ * (4 * dist x₀ x) ^ (δ : ℝ) := by
  let t := dist x₀ x
  have ht : 0 < t := dist_pos.mpr hxx
  let N : Set X := {y | dist x₀ y ≤ 2 * t}
  let F : Set X := {y | 2 * t < dist x₀ y}
  have hN : MeasurableSet N := measurableSet_le (continuous_const.dist continuous_id).measurable measurable_const
  have hF : MeasurableSet F := measurableSet_lt measurable_const (continuous_const.dist continuous_id).measurable
  have hNF : G \ N = G ∩ F := by ext y; simp only [mem_sdiff, mem_inter_iff, N, F, mem_ofPred_eq, not_le]
  have hi₀ := (hK.regularized_absolute hδ hf hx₀).1
  have hi₁ := (hK.regularized_absolute hδ hf hx).1
  have he₀ := integral_inter_add_sdiff hN hi₀
  have he₁ := integral_inter_add_sdiff hN hi₁
  rw [hNF] at he₀ he₁
  have hfar := hK.regularized_far_difference d hCan hδ hδβ hf hx₀ hx hxx hκ
  have hn₀ := hK.regularized_near_le hδ hf hx₀ hN
    (r := 3 * t) (by linarith) (by dsimp [t]; linarith [D.κ_pos]) (by
      intro y hy
      have hyN : dist x₀ y ≤ 2 * t := hy.2
      linarith)
  have hn₁ := hK.regularized_near_le hδ hf hx hN
    (r := 4 * t) (by linarith) (by dsimp [t]; linarith [D.κ_pos]) (by
      intro y hy
      have hyN : dist x₀ y ≤ 2 * t := hy.2
      have htri := dist_triangle x x₀ y
      rw [dist_comm x x₀] at htri
      linarith)
  have hif₀ : IntegrableOn (fun y => K x₀ y * (f y - f x₀)) (G ∩ F) D.μ := hi₀.mono_set inter_subset_left
  have hif₁ : IntegrableOn (fun y => K x y * (f y - f x)) (G ∩ F) D.μ := hi₁.mono_set inter_subset_left
  have hsub : (∫ y in G ∩ F, K x y * (f y - f x) - K x₀ y * (f y - f x₀) ∂D.μ) =
      (∫ y in G ∩ F, K x y * (f y - f x) ∂D.μ) - ∫ y in G ∩ F, K x₀ y * (f y - f x₀) ∂D.μ := by
    rw [← integral_sub hif₁ hif₀]
  rw [hsub] at hfar
  unfold regularizedIntegral
  rw [← he₁, ← he₀]
  have hb := abs_add_le ((∫ y in G ∩ F, K x y * (f y - f x) ∂D.μ) -
    ∫ y in G ∩ F, K x₀ y * (f y - f x₀) ∂D.μ)
    ((∫ y in G ∩ N, K x y * (f y - f x) ∂D.μ) - ∫ y in G ∩ N, K x₀ y * (f y - f x₀) ∂D.μ)
  have hb' := abs_sub (∫ y in G ∩ N, K x y * (f y - f x) ∂D.μ)
    (∫ y in G ∩ N, K x₀ y * (f y - f x₀) ∂D.μ)
  have he : |(∫ y in G ∩ N, K x y * (f y - f x) ∂D.μ) + (∫ y in G ∩ F, K x y * (f y - f x) ∂D.μ) -
      ((∫ y in G ∩ N, K x₀ y * (f y - f x₀) ∂D.μ) + (∫ y in G ∩ F, K x₀ y * (f y - f x₀) ∂D.μ))| =
      |(∫ y in G ∩ F, K x y * (f y - f x) ∂D.μ) - (∫ y in G ∩ F, K x₀ y * (f y - f x₀) ∂D.μ) +
        ((∫ y in G ∩ N, K x y * (f y - f x) ∂D.μ) - ∫ y in G ∩ N, K x₀ y * (f y - f x₀) ∂D.μ)| := by congr 1; ring
  rw [he]
  dsimp [t] at hn₀ hn₁
  linarith

end RothschildStein.H2

-- Copyright (c) 2026 Scott Armstrong and Amélie Loher. All rights reserved.
-- Released under Apache 2.0 license as described in the file LICENSE.
module

public import RothschildStein.H2.FractionalHolderFar

set_option autoImplicit false
set_option relaxedAutoImplicit false

@[expose] public section
noncomputable section
open Set MeasureTheory Metric
open scoped ENNReal

namespace RothschildStein.H2
variable {X : Type*} [MetricSpace X] [MeasurableSpace X] [BorelSpace X]

/-- The small-distance Hölder split, BB p. 305: a strict far region
and a closed near region, with the two near centers treated separately. -/
theorem SupportedKernel.fractional_small_difference {D : LocDoubling X} {E G : Set X}
    {β ν A S R : ℝ} {K : X → X → ℝ} (hK : SupportedKernel D E G β ν A S R K)
    {α : ℝ} (hα : 0 < α) (hαβ : α ≤ β) (hαν : α < ν)
    {f : X → ℝ} (hf : AEStronglyMeasurable f (D.μ.restrict G))
    {M : ℝ} (hM : 0 ≤ M) (hfb : ∀ᵐ y ∂D.μ.restrict G, |f y| ≤ M)
    {x₀ x : X} (hx₀ : x₀ ∈ E) (hx : x ∈ E) (hxx : x₀ ≠ x)
    (hκ : dist x₀ x < D.κ / 3) :
    |fractionalIntegral D.μ G K f x₀ - fractionalIntegral D.μ G K f x| ≤
      S * M * dist x₀ x ^ α * volumeIntegralConstant D.C_D (ν - α) *
        (R + dist x₀ x) ^ (ν - α) +
      A * M * volumeIntegralConstant D.C_D ν * (3 * dist x₀ x) ^ ν +
      A * M * volumeIntegralConstant D.C_D ν * (4 * dist x₀ x) ^ ν := by
  let t := dist x₀ x
  have ht : 0 < t := dist_pos.mpr hxx
  let N : Set X := {y | dist x₀ y ≤ 2 * t}
  let F : Set X := {y | 2 * t < dist x₀ y}
  have hN : MeasurableSet N := measurableSet_le (continuous_const.dist continuous_id).measurable measurable_const
  have hF : MeasurableSet F := measurableSet_lt measurable_const (continuous_const.dist continuous_id).measurable
  have hNF : G \ N = G ∩ F := by ext y; simp only [mem_sdiff, mem_inter_iff, N, F, mem_ofPred_eq, not_le]
  have hi₀ := (hK.fractional_absolute (hα.trans hαν) hf hM hfb hx₀).1
  have hi₁ := (hK.fractional_absolute (hα.trans hαν) hf hM hfb hx).1
  have he₀ := integral_inter_add_sdiff hN hi₀
  have he₁ := integral_inter_add_sdiff hN hi₁
  rw [hNF] at he₀ he₁
  have hfar := hK.fractional_far_le hα hαβ hαν hf hM hfb hx₀ hx hxx hκ
  have hn₀ := hK.fractional_near_le (hα.trans hαν) hf hM hfb hx₀ hN
    (r := 3 * t) (by linarith) (by dsimp [t]; linarith [D.κ_pos]) (by
      intro y hy
      have hyN : dist x₀ y ≤ 2 * t := hy.2
      linarith)
  have hn₁ := hK.fractional_near_le (hα.trans hαν) hf hM hfb hx hN
    (r := 4 * t) (by linarith) (by dsimp [t]; linarith [D.κ_pos]) (by
      intro y hy
      have hyN : dist x₀ y ≤ 2 * t := hy.2
      have htri := dist_triangle x x₀ y
      rw [dist_comm x x₀] at htri
      linarith)
  have hif₀ : IntegrableOn (fun y => K x₀ y * f y) (G ∩ F) D.μ := hi₀.mono_set inter_subset_left
  have hif₁ : IntegrableOn (fun y => K x y * f y) (G ∩ F) D.μ := hi₁.mono_set inter_subset_left
  have hsub : (∫ y in G ∩ F, (K x₀ y - K x y) * f y ∂D.μ) =
      (∫ y in G ∩ F, K x₀ y * f y ∂D.μ) - ∫ y in G ∩ F, K x y * f y ∂D.μ := by
    rw [← integral_sub hif₀ hif₁]
    congr 1
    funext y
    ring
  rw [hsub] at hfar
  unfold fractionalIntegral
  rw [← he₀, ← he₁]
  have hb := abs_add_le (∫ y in G ∩ F, K x₀ y * f y ∂D.μ - ∫ y in G ∩ F, K x y * f y ∂D.μ)
    (∫ y in G ∩ N, K x₀ y * f y ∂D.μ - ∫ y in G ∩ N, K x y * f y ∂D.μ)
  have hb' := abs_sub (∫ y in G ∩ N, K x₀ y * f y ∂D.μ) (∫ y in G ∩ N, K x y * f y ∂D.μ)
  have he : |(∫ y in G ∩ N, K x₀ y * f y ∂D.μ) + (∫ y in G ∩ F, K x₀ y * f y ∂D.μ) -
      ((∫ y in G ∩ N, K x y * f y ∂D.μ) + (∫ y in G ∩ F, K x y * f y ∂D.μ))| =
      |(∫ y in G ∩ F, K x₀ y * f y ∂D.μ) - (∫ y in G ∩ F, K x y * f y ∂D.μ) +
        ((∫ y in G ∩ N, K x₀ y * f y ∂D.μ) - ∫ y in G ∩ N, K x y * f y ∂D.μ)| := by congr 1; ring
  rw [he]
  dsimp [t] at hn₀ hn₁
  linarith

end RothschildStein.H2

-- Copyright (c) 2026 Scott Armstrong and Amélie Loher. All rights reserved.
-- Released under Apache 2.0 license as described in the file LICENSE.
module

public import Hormander.A.Mollifier.Defs
public import Mathlib.Analysis.Calculus.ContDiff.Bounds

@[expose] public section

noncomputable section

open ContinuousLinearMap SchwartzMap

namespace Hormander.A

/-- Iterated derivatives of a dilated Schwartz function scale by `δ ^ i`. -/
theorem norm_iteratedFDeriv_dilate_le {N : ℕ} (g : 𝓢(Carrier N, ℂ)) {δ : ℝ} (hδ : 0 ≤ δ)
    (i : ℕ) (ξ : Carrier N) :
    ‖iteratedFDeriv ℝ i (fun ξ : Carrier N => g (δ • ξ)) ξ‖ ≤
      δ ^ i * SchwartzMap.seminorm ℂ 0 i g := by
  have hcomp : (fun ξ : Carrier N => g (δ • ξ)) =
      (g : Carrier N → ℂ) ∘ ⇑(δ • ContinuousLinearMap.id ℝ (Carrier N)) := by
    funext ξ
    simp
  rw [hcomp, ContinuousLinearMap.iteratedFDeriv_comp_right _ (g.smooth (i : ℕ∞)) ξ
    (by exact_mod_cast le_rfl)]
  refine (ContinuousMultilinearMap.norm_compContinuousLinearMap_le _ _).trans ?_
  have hn : ‖δ • ContinuousLinearMap.id ℝ (Carrier N)‖ ≤ δ := by
    calc ‖δ • ContinuousLinearMap.id ℝ (Carrier N)‖
        ≤ ‖δ‖ * ‖ContinuousLinearMap.id ℝ (Carrier N)‖ := ContinuousLinearMap.opNorm_smul_le _ _
      _ ≤ ‖δ‖ * 1 := by gcongr; exact ContinuousLinearMap.norm_id_le
      _ = δ := by rw [mul_one, Real.norm_eq_abs, abs_of_nonneg hδ]
  have hprod : ∏ _ : Fin i, ‖δ • ContinuousLinearMap.id ℝ (Carrier N)‖ ≤ δ ^ i := by
    calc ∏ _ : Fin i, ‖δ • ContinuousLinearMap.id ℝ (Carrier N)‖
        ≤ ∏ _ : Fin i, δ := by gcongr
      _ = δ ^ i := by simp
  calc ‖iteratedFDeriv ℝ i (⇑g) (δ • ξ)‖ * ∏ _ : Fin i, ‖δ • ContinuousLinearMap.id ℝ (Carrier N)‖
      ≤ SchwartzMap.seminorm ℂ 0 i g * δ ^ i := by
        gcongr
        exact SchwartzMap.norm_iteratedFDeriv_le_seminorm ℂ g i _
    _ = _ := mul_comm _ _


/-- Dilated Schwartz functions are smooth. -/
theorem contDiff_dilate {N : ℕ} (g : 𝓢(Carrier N, ℂ)) (δ : ℝ) (n : ℕ∞) :
    ContDiff ℝ n (fun ξ : Carrier N => g (δ • ξ)) :=
  (g.smooth n).comp (contDiff_const_smul δ)

/-- Mean value estimate for a dilated Schwartz function normalised at the origin. -/
theorem norm_dilate_sub_one_le {N : ℕ} (g : 𝓢(Carrier N, ℂ)) (hg0 : g 0 = 1) {δ : ℝ}
    (hδ : 0 ≤ δ) (ξ : Carrier N) :
    ‖g (δ • ξ) - 1‖ ≤ SchwartzMap.seminorm ℂ 0 1 g * (δ * ‖ξ‖) := by
  have h := (convex_univ (𝕜 := ℝ) (E := Carrier N)).norm_image_sub_le_of_norm_fderiv_le
    (f := ⇑g) (C := SchwartzMap.seminorm ℂ 0 1 g) (fun x _ => g.differentiableAt)
    (fun x _ => by
      have := SchwartzMap.norm_iteratedFDeriv_le_seminorm ℂ g 1 x
      rwa [norm_iteratedFDeriv_one] at this)
    (Set.mem_univ 0) (Set.mem_univ (δ • ξ))
  rw [hg0, sub_zero, norm_smul, Real.norm_eq_abs, abs_of_nonneg hδ] at h
  exact h

/-- The `i`-th derivative of `g (δ ·) - 1` is `O(δ (1 + ‖ξ‖))` for `δ ≤ 1`. -/
theorem norm_iteratedFDeriv_dilate_sub_one_le {N : ℕ} (g : 𝓢(Carrier N, ℂ)) (hg0 : g 0 = 1)
    {δ : ℝ} (hδ0 : 0 ≤ δ) (hδ1 : δ ≤ 1) (i : ℕ) (ξ : Carrier N) :
    ‖iteratedFDeriv ℝ i (fun ξ : Carrier N => g (δ • ξ) - 1) ξ‖ ≤
      δ * ((SchwartzMap.seminorm ℂ 0 1 g + SchwartzMap.seminorm ℂ 0 i g) * (1 + ‖ξ‖)) := by
  have h1 : 0 ≤ SchwartzMap.seminorm ℂ 0 1 g := apply_nonneg _ _
  have hi : 0 ≤ SchwartzMap.seminorm ℂ 0 i g := apply_nonneg _ _
  rcases Nat.eq_zero_or_pos i with rfl | hpos
  · rw [norm_iteratedFDeriv_zero]
    refine (norm_dilate_sub_one_le g hg0 hδ0 ξ).trans ?_
    have hξ := norm_nonneg ξ
    nlinarith [mul_nonneg hδ0 hξ, mul_nonneg hδ0 (mul_nonneg h1 hξ), mul_nonneg hδ0 hi,
      mul_nonneg hδ0 (mul_nonneg hi hξ)]
  · obtain ⟨j, rfl⟩ := Nat.exists_eq_succ_of_ne_zero hpos.ne'
    have hsub : iteratedFDeriv ℝ (j + 1) (fun ξ : Carrier N => g (δ • ξ) - 1) ξ =
        iteratedFDeriv ℝ (j + 1) (fun ξ : Carrier N => g (δ • ξ)) ξ := by
      have hfun : (fun ξ : Carrier N => g (δ • ξ) - 1) =
          (fun ξ : Carrier N => g (δ • ξ)) - fun _ => (1 : ℂ) := rfl
      rw [hfun, iteratedFDeriv_sub_apply (contDiff_dilate g δ _).contDiffAt contDiffAt_const,
        iteratedFDeriv_const_of_ne (Nat.succ_ne_zero j)]
      simp
    rw [hsub]
    refine (norm_iteratedFDeriv_dilate_le g hδ0 (j + 1) ξ).trans ?_
    have hpow : δ ^ (j + 1) ≤ δ := pow_le_of_le_one hδ0 hδ1 (Nat.succ_ne_zero j)
    have hξ := norm_nonneg ξ
    calc δ ^ (j + 1) * SchwartzMap.seminorm ℂ 0 (j + 1) g
        ≤ δ * SchwartzMap.seminorm ℂ 0 (j + 1) g := by gcongr
      _ ≤ δ * ((SchwartzMap.seminorm ℂ 0 1 g + SchwartzMap.seminorm ℂ 0 (j + 1) g) *
          (1 + ‖ξ‖)) := by
        gcongr
        nlinarith [mul_nonneg h1 hξ, mul_nonneg hi hξ]


/-- The `δ`-independent constant in the Schwartz seminorm estimate for dilation multipliers. -/
def dilationConst {N : ℕ} (g φ : 𝓢(Carrier N, ℂ)) (k n : ℕ) : ℝ :=
  ∑ i ∈ Finset.range (n + 1), (n.choose i : ℝ) *
    ((SchwartzMap.seminorm ℂ 0 1 g + SchwartzMap.seminorm ℂ 0 i g) *
      (SchwartzMap.seminorm ℂ k (n - i) φ + SchwartzMap.seminorm ℂ (k + 1) (n - i) φ))

/-- The dilation constant is nonnegative. -/
theorem dilationConst_nonneg {N : ℕ} (g φ : 𝓢(Carrier N, ℂ)) (k n : ℕ) :
    0 ≤ dilationConst g φ k n := by
  unfold dilationConst
  refine Finset.sum_nonneg fun i _ => ?_
  have h1 : 0 ≤ SchwartzMap.seminorm ℂ 0 1 g := apply_nonneg _ _
  have h2 : 0 ≤ SchwartzMap.seminorm ℂ 0 i g := apply_nonneg _ _
  have h3 : 0 ≤ SchwartzMap.seminorm ℂ k (n - i) φ := apply_nonneg _ _
  have h4 : 0 ≤ SchwartzMap.seminorm ℂ (k + 1) (n - i) φ := apply_nonneg _ _
  positivity

/-- Pointwise bound for one Leibniz term. -/
theorem leibniz_term_le {c a b x s₀ s₁ δ A : ℝ} {k : ℕ} (hc : 0 ≤ c) (ha : a ≤ δ * (A * (1 + x)))
    (hx : 0 ≤ x) (hb : 0 ≤ b) (hδ : 0 ≤ δ) (hA : 0 ≤ A)
    (h₀ : x ^ k * b ≤ s₀) (h₁ : x ^ (k + 1) * b ≤ s₁) :
    x ^ k * (c * a * b) ≤ δ * (c * (A * (s₀ + s₁))) := by
  have hxk : 0 ≤ x ^ k * b := by positivity
  calc x ^ k * (c * a * b) = c * a * (x ^ k * b) := by ring
    _ ≤ c * (δ * (A * (1 + x))) * (x ^ k * b) := by gcongr
    _ = δ * (c * (A * (x ^ k * b + x ^ (k + 1) * b))) := by ring
    _ ≤ δ * (c * (A * (s₀ + s₁))) := by gcongr

/-- The key seminorm estimate: multiplication by `g (δ ·) - 1` is `O(δ)` in every seminorm. -/
theorem seminorm_smulLeft_dilate_sub_le {N : ℕ} (g φ : 𝓢(Carrier N, ℂ)) (hg0 : g 0 = 1)
    {δ : ℝ} (hδ0 : 0 ≤ δ) (hδ1 : δ ≤ 1)
    (hT : (fun ξ : Carrier N => g (δ • ξ)).HasTemperateGrowth) (k n : ℕ) :
    SchwartzMap.seminorm ℂ k n
        (SchwartzMap.smulLeftCLM ℂ (fun ξ : Carrier N => g (δ • ξ)) φ - φ) ≤
      δ * dilationConst g φ k n := by
  refine SchwartzMap.seminorm_le_bound ℂ k n _ (mul_nonneg hδ0 (dilationConst_nonneg g φ k n))
    fun ξ => ?_
  have hfun : ⇑(SchwartzMap.smulLeftCLM ℂ (fun ξ : Carrier N => g (δ • ξ)) φ - φ) =
      fun ξ : Carrier N => (g (δ • ξ) - 1) * φ ξ := by
    funext ξ
    rw [sub_apply, SchwartzMap.smulLeftCLM_apply_apply hT, smul_eq_mul, sub_mul,
      one_mul]
  rw [hfun]
  have hf : ContDiff ℝ (n : ℕ∞) (fun ξ : Carrier N => g (δ • ξ) - 1) :=
    (contDiff_dilate g δ n).sub contDiff_const
  have hmul := norm_iteratedFDeriv_mul_le (𝕜 := ℝ) hf (φ.smooth n) ξ (n := n) le_rfl
  have hxk : 0 ≤ ‖ξ‖ ^ k := by positivity
  calc ‖ξ‖ ^ k * ‖iteratedFDeriv ℝ n (fun y : Carrier N => (g (δ • y) - 1) * φ y) ξ‖
      ≤ ‖ξ‖ ^ k * ∑ i ∈ Finset.range (n + 1), (n.choose i : ℝ) *
        ‖iteratedFDeriv ℝ i (fun ξ : Carrier N => g (δ • ξ) - 1) ξ‖ *
          ‖iteratedFDeriv ℝ (n - i) φ ξ‖ := mul_le_mul_of_nonneg_left hmul hxk
    _ = ∑ i ∈ Finset.range (n + 1), ‖ξ‖ ^ k * ((n.choose i : ℝ) *
        ‖iteratedFDeriv ℝ i (fun ξ : Carrier N => g (δ • ξ) - 1) ξ‖ *
          ‖iteratedFDeriv ℝ (n - i) φ ξ‖) := by rw [Finset.mul_sum]
    _ ≤ ∑ i ∈ Finset.range (n + 1), δ * ((n.choose i : ℝ) *
        ((SchwartzMap.seminorm ℂ 0 1 g + SchwartzMap.seminorm ℂ 0 i g) *
          (SchwartzMap.seminorm ℂ k (n - i) φ + SchwartzMap.seminorm ℂ (k + 1) (n - i) φ))) := by
      refine Finset.sum_le_sum fun i _ => ?_
      have h1 : 0 ≤ SchwartzMap.seminorm ℂ 0 1 g := apply_nonneg _ _
      have h2 : 0 ≤ SchwartzMap.seminorm ℂ 0 i g := apply_nonneg _ _
      exact leibniz_term_le (Nat.cast_nonneg _)
        (norm_iteratedFDeriv_dilate_sub_one_le g hg0 hδ0 hδ1 i ξ) (norm_nonneg ξ)
        (norm_nonneg _) hδ0 (add_nonneg h1 h2)
        (SchwartzMap.le_seminorm ℂ k (n - i) φ ξ) (SchwartzMap.le_seminorm ℂ (k + 1) (n - i) φ ξ)
    _ = δ * dilationConst g φ k n := by rw [dilationConst, Finset.mul_sum]

end Hormander.A

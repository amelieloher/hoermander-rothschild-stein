-- Copyright (c) 2026 Scott Armstrong and Amélie Loher. All rights reserved.
-- Released under Apache 2.0 license as described in the file LICENSE.
module

public import Mathlib.MeasureTheory.Function.L2Space
public import HeatKernel.Kernel.HeatEvaluations
public import Mathlib.MeasureTheory.Measure.OpenPos

/-! # Positivity detected by L² pairings

Testing against the negative part identifies the positive cone in real L².
-/

@[expose] public section

noncomputable section

open MeasureTheory

namespace HeatKernel

/-- A real L² vector pairing nonnegatively with every nonnegative vector is nonnegative. -/
theorem ae_nonneg_of_inner_nonneg {X : Type*} [MeasurableSpace X] (μ : Measure X)
    (q : Lp ℝ 2 μ)
    (h : ∀ f : Lp ℝ 2 μ, (∀ᵐ x ∂μ, 0 ≤ f x) → 0 ≤ inner ℝ q f) :
    ∀ᵐ x ∂μ, 0 ≤ q x := by
  let f := Lp.negPart q
  have hf : ∀ᵐ x ∂μ, f x = max (-q x) 0 := Lp.coeFn_negPart_eq_max q
  have hnon : ∀ᵐ x ∂μ, 0 ≤ f x := hf.mono fun x hx => hx ▸ le_max_right _ _
  have hpair : inner ℝ q f = -inner ℝ f f := by
    rw [L2.inner_def, L2.inner_def, ← integral_neg]
    apply integral_congr_ae
    filter_upwards [hf] with x hx
    simp only [RCLike.inner_apply, conj_trivial]
    rw [hx]
    by_cases hqx : 0 ≤ q x
    · rw [max_eq_right (neg_nonpos.mpr hqx)]
      simp
    · rw [max_eq_left (neg_nonneg.mpr (le_of_not_ge hqx))]
      ring
  have hzero : inner ℝ f f = 0 := le_antisymm (by linarith [h f hnon])
    (real_inner_self_nonneg)
  have hfzero : f = 0 := (inner_self_eq_zero (𝕜 := ℝ)).mp hzero
  have hfae : ∀ᵐ x ∂μ, f x = 0 := by
    filter_upwards [Lp.coeFn_zero ℝ 2 μ] with x hx
    simpa only [hfzero, Pi.zero_apply] using hx
  filter_upwards [hf, hfae] with x hx hz
  have : -q x ≤ 0 := (le_max_left (-q x) 0).trans (by rw [← hx, hz])
  linarith

/-- A positive bounded L² functional has a nonnegative Riesz vector. -/
theorem ae_nonneg_evaluationVector {X A : Type*} [MeasurableSpace X] (μ : Measure X)
    (L : A → Lp ℝ 2 μ →L[ℝ] ℝ)
    (hL : ∀ a f, (∀ᵐ x ∂μ, 0 ≤ f x) → 0 ≤ L a f) (a : A) :
    ∀ᵐ x ∂μ, 0 ≤ evaluationVector L a x := by
  apply ae_nonneg_of_inner_nonneg μ (evaluationVector L a)
  intro f hf
  rw [inner_evaluationVector]
  exact hL a f hf

/-- Kernels of positive L² evaluation maps are pointwise nonnegative. -/
theorem evaluationKernel_nonneg_of_positive {X A : Type*} [MeasurableSpace X] (μ : Measure X)
    (L : ℝ → A → Lp ℝ 2 μ →L[ℝ] ℝ)
    (hL : ∀ t a f, (∀ᵐ x ∂μ, 0 ≤ f x) → 0 ≤ L t a f)
    (t : ℝ) (a b : A) : 0 ≤ evaluationKernel L t a b := by
  rw [evaluationKernel, L2.inner_def]
  apply integral_nonneg_of_ae
  filter_upwards [ae_nonneg_evaluationVector μ (L (t / 2)) (hL (t / 2)) a,
    ae_nonneg_evaluationVector μ (L (t / 2)) (hL (t / 2)) b] with x hx hy
  simpa only [Real.inner_apply, Pi.zero_apply] using mul_nonneg hx hy

/-- Positive semigroup representatives give a nonnegative kernel at all points. -/
theorem heatRepresentativeKernel_nonneg {n : ℕ}
    (T : ℝ → Lp ℝ 2 (volume : Measure (Fin n → ℝ)) →L[ℝ]
      Lp ℝ 2 (volume : Measure (Fin n → ℝ)))
    (u : ℝ → Lp ℝ 2 (volume : Measure (Fin n → ℝ)) → (Fin n → ℝ) → ℝ)
    (hu : ∀ t, 0 < t → ∀ f, Continuous (u t f))
    (hae : ∀ t, 0 < t → ∀ f, T t f =ᵐ[volume] u t f)
    (hpos : ∀ t, 0 < t → ∀ f, (∀ᵐ x ∂volume, 0 ≤ f x) →
      ∀ᵐ x ∂volume, 0 ≤ T t f x) (t : ℝ) (a b : Fin n → ℝ) :
    0 ≤ evaluationKernel (heatRepresentativeEvaluation T u hu hae) t a b := by
  apply evaluationKernel_nonneg_of_positive volume
  intro s x f hf
  by_cases hs : 0 < s
  · rw [heatRepresentativeEvaluation_apply T u hu hae hs]
    have hnon : ∀ᵐ y ∂volume, 0 ≤ u s f y := by
      filter_upwards [hpos s hs f hf, hae s hs f] with y hy heq
      rwa [← heq]
    have heq : (fun y => max (u s f y) 0) = u s f := by
      apply Measure.eq_of_ae_eq (hnon.mono fun y hy => max_eq_left hy)
        ((hu s hs f).max continuous_const) (hu s hs f)
    rw [← congrFun heq x]
    exact le_max_right _ _
  · simp [heatRepresentativeEvaluation, hs]

end HeatKernel

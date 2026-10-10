-- Copyright (c) 2026 Scott Armstrong and Amélie Loher. All rights reserved.
-- Released under Apache 2.0 license as described in the file LICENSE.
module

public import HeatKernel.Kernel.EvaluationKernel
public import Mathlib.MeasureTheory.Integral.Bochner.Basic

/-! # Semigroup identities for evaluation kernels

Self-adjointness and the semigroup law identify the inner product of evaluation
vectors at unequal times with the kernel at their sum.
-/

@[expose] public section

noncomputable section

open MeasureTheory

namespace HeatKernel

variable {H A : Type*} [NormedAddCommGroup H] [InnerProductSpace ℝ H] [CompleteSpace H]

/-- The semigroup law transfers to the mixed-time inner product of Riesz vectors. -/
theorem inner_evaluationVector_eq_kernel_of_semigroup
    (L : ℝ → A → H →L[ℝ] ℝ) (T : ℝ → H →L[ℝ] H)
    (hT : ∀ s, 0 ≤ s → IsSelfAdjoint (T s))
    (hlaw : ∀ s t, 0 ≤ s → 0 < t → ∀ x f, L (t + s) x f = L t x (T s f))
    (hsemigroup : ∀ s t, 0 ≤ s → 0 ≤ t → T (s + t) = (T s).comp (T t))
    {s t : ℝ} (hs : 0 < s) (ht : 0 < t) (x y : A) :
    inner ℝ (evaluationVector (L s) x) (evaluationVector (L t) y) =
      evaluationKernel L (s + t) x y := by
  have hs₂ : 0 < s / 2 := div_pos hs (by norm_num)
  have ht₂ : 0 < t / 2 := div_pos ht (by norm_num)
  have hvec (a b : ℝ) (ha : 0 < a) (hb : 0 ≤ b) (z : A) :
      evaluationVector (L (a + b)) z = T b (evaluationVector (L a) z) :=
    evaluationVector_add_of_selfAdjoint L T (hT b hb) (hlaw b a hb ha) z
  have hcomm (u : H) : T (s / 2) (T (t / 2) u) = T (t / 2) (T (s / 2) u) := by
    have h := congrArg (fun S : H →L[ℝ] H => S u)
      ((hsemigroup (s / 2) (t / 2) hs₂.le ht₂.le).symm.trans
        ((congrArg T (add_comm (s / 2) (t / 2))).trans
          (hsemigroup (t / 2) (s / 2) ht₂.le hs₂.le)))
    exact h
  have hqx : evaluationVector (L s) x = T (s / 2) (evaluationVector (L (s / 2)) x) := by
    simpa only [add_halves] using hvec (s / 2) (s / 2) hs₂ hs₂.le x
  have hqy : evaluationVector (L t) y = T (t / 2) (evaluationVector (L (t / 2)) y) := by
    simpa only [add_halves] using hvec (t / 2) (t / 2) ht₂ ht₂.le y
  have hcx : evaluationVector (L ((s + t) / 2)) x =
      T (t / 2) (evaluationVector (L (s / 2)) x) := by
    simpa only [add_div] using hvec (s / 2) (t / 2) hs₂ ht₂.le x
  have hcy : evaluationVector (L ((s + t) / 2)) y =
      T (s / 2) (evaluationVector (L (t / 2)) y) := by
    simpa only [add_div, add_comm] using hvec (t / 2) (s / 2) ht₂ hs₂.le y
  rw [hqx, hqy, evaluationKernel, hcx, hcy]
  exact ((hT (s / 2) hs₂.le).isSymmetric (evaluationVector (L (s / 2)) x)
    (T (t / 2) (evaluationVector (L (t / 2)) y))).trans
    ((congrArg (inner ℝ (evaluationVector (L (s / 2)) x))
      (hcomm (evaluationVector (L (t / 2)) y))).trans
      ((hT (t / 2) ht₂.le).isSymmetric (evaluationVector (L (s / 2)) x)
        (T (s / 2) (evaluationVector (L (t / 2)) y))).symm)

/-- A semigroup representative identity identifies each kernel section with its Riesz vector. -/
theorem ae_evaluationKernel_eq_representation [MeasurableSpace A] (μ : Measure A)
    (L : ℝ → A → H →L[ℝ] ℝ) (T : ℝ → H →L[ℝ] H) (rep : H → A → ℝ)
    {t : ℝ} (_ht : 0 < t) (hT : IsSelfAdjoint (T (t / 2)))
    (hlaw : ∀ x f, L (t / 2 + t / 2) x f = L (t / 2) x (T (t / 2) f))
    (hrep : ∀ f, (fun y => L (t / 2) y f) =ᵐ[μ] rep (T (t / 2) f)) (x : A) :
    (fun y => evaluationKernel L t x y) =ᵐ[μ] rep (evaluationVector (L t) x) := by
  have hq : evaluationVector (L t) x =
      T (t / 2) (evaluationVector (L (t / 2)) x) := by
    simpa only [add_halves] using evaluationVector_add_of_selfAdjoint L T hT hlaw x
  filter_upwards [hrep (evaluationVector (L (t / 2)) x)] with y hy
  rw [evaluationKernel_eq_evaluation, hy, hq]

/-- Hilbert pairing and section representatives give the pointwise integral composition law. -/
theorem integral_evaluationKernel_mul_of_pairing [MeasurableSpace A] (μ : Measure A)
    (L : ℝ → A → H →L[ℝ] ℝ) (T : ℝ → H →L[ℝ] H) (rep : H → A → ℝ)
    (hT : ∀ s, 0 ≤ s → IsSelfAdjoint (T s))
    (hlaw : ∀ s t, 0 ≤ s → 0 < t → ∀ x f, L (t + s) x f = L t x (T s f))
    (hsemigroup : ∀ s t, 0 ≤ s → 0 ≤ t → T (s + t) = (T s).comp (T t))
    (hrep : ∀ t, 0 < t → ∀ f, (fun y => L t y f) =ᵐ[μ] rep (T t f))
    (hpair : ∀ u v, ∫ z, rep u z * rep v z ∂μ = inner ℝ u v)
    {s t : ℝ} (hs : 0 < s) (ht : 0 < t) (x y : A) :
    ∫ z, evaluationKernel L s x z * evaluationKernel L t z y ∂μ =
      evaluationKernel L (s + t) x y := by
  have hs₂ : 0 < s / 2 := half_pos hs
  have ht₂ : 0 < t / 2 := half_pos ht
  have hx := ae_evaluationKernel_eq_representation μ L T rep hs (hT _ hs₂.le)
    (hlaw _ _ hs₂.le hs₂) (hrep _ hs₂) x
  have hy := ae_evaluationKernel_eq_representation μ L T rep ht (hT _ ht₂.le)
    (hlaw _ _ ht₂.le ht₂) (hrep _ ht₂) y
  calc
    ∫ z, evaluationKernel L s x z * evaluationKernel L t z y ∂μ =
        ∫ z, rep (evaluationVector (L s) x) z * rep (evaluationVector (L t) y) z ∂μ := by
      apply integral_congr_ae
      filter_upwards [hx, hy] with z hz₁ hz₂
      rw [hz₁, evaluationKernel_symm L t z y, hz₂]
    _ = inner ℝ (evaluationVector (L s) x) (evaluationVector (L t) y) := hpair _ _
    _ = evaluationKernel L (s + t) x y :=
      inner_evaluationVector_eq_kernel_of_semigroup L T hT hlaw hsemigroup hs ht x y

end HeatKernel

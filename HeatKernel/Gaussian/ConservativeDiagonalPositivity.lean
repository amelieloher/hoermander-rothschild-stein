-- Copyright (c) 2026 Scott Armstrong and Amélie Loher. All rights reserved.
-- Released under Apache 2.0 license as described in the file LICENSE.
module

public import HeatKernel.Kernel.ConservativeHorizontalHeatKernel
public import HeatKernel.Gaussian.NaturalKernelScaling
public import Mathlib.MeasureTheory.Function.L2Space
import Mathlib.Tactic

/-! # Strict diagonal positivity from conservation

A row with nonzero integral has a positive quadratic integral. Symmetry and
Chapman–Kolmogorov identify that integral with the diagonal at twice the time.
-/

@[expose] public section
set_option autoImplicit false
set_option relaxedAutoImplicit false
noncomputable section
open Set MeasureTheory RothschildStein
namespace HeatKernel.Gaussian

/-- A square-integrable real function with nonzero integral has positive quadratic integral. -/
theorem integral_sq_pos_of_integral_ne_zero {α : Type*} [MeasurableSpace α]
    (μ : Measure α) (f : α → ℝ) (hf : MemLp f 2 μ)
    (hm : (∫ z, f z ∂μ) ≠ 0) : 0 < ∫ z, f z ^ 2 ∂μ := by
  have hn : 0 ≤ ∫ z, f z ^ 2 ∂μ := integral_nonneg (fun z ↦ sq_nonneg (f z))
  by_contra h
  have hz : (∫ z, f z ^ 2 ∂μ) = 0 := le_antisymm (le_of_not_gt h) hn
  have hae := (integral_eq_zero_iff_of_nonneg (fun z ↦ sq_nonneg (f z))
    hf.integrable_sq).mp hz
  have hfzero : f =ᵐ[μ] 0 := hae.mono (fun z hz ↦ sq_eq_zero_iff.mp hz)
  apply hm
  simpa only [Pi.zero_apply, integral_zero] using integral_congr_ae hfzero

/-- Conservation, symmetry and composition imply strict positivity at every positive-time diagonal. -/
theorem kernel_diagonal_pos_of_conservation {α : Type*} [MeasurableSpace α]
    (μ : Measure α) (p : ℝ → α → α → ℝ)
    (hL2 : ∀ s, 0 < s → ∀ x, MemLp (p s x) 2 μ)
    (hmass : ∀ s, 0 < s → ∀ x, (∫ z, p s x z ∂μ) = 1)
    (hsym : ∀ s, 0 < s → ∀ x y, p s x y = p s y x)
    (hconv : ∀ s t, 0 < s → 0 < t → ∀ x y,
      (∫ z, p s x z * p t z y ∂μ) = p (s + t) x y)
    {t : ℝ} (ht : 0 < t) (x : α) : 0 < p t x x := by
  have hs : 0 < t / 2 := by positivity
  have hp := integral_sq_pos_of_integral_ne_zero μ (p (t / 2) x) (hL2 _ hs x)
    (by rw [hmass _ hs x]; norm_num)
  have he : (∫ z, p (t / 2) x z ^ 2 ∂μ) = p t x x := by
    calc
      _ = ∫ z, p (t / 2) x z * p (t / 2) z x ∂μ := by
        apply integral_congr_ae
        exact Filter.Eventually.of_forall (fun z ↦ by dsimp only; rw [hsym _ hs z x, pow_two])
      _ = p (t / 2 + t / 2) x x := hconv _ _ hs hs x x
      _ = p t x x := by congr 1; ring
  rwa [he] at hp

end HeatKernel.Gaussian

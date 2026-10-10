-- Copyright (c) 2026 Scott Armstrong and Amélie Loher. All rights reserved.
-- Released under Apache 2.0 license as described in the file LICENSE.
module

public import Mathlib.MeasureTheory.Function.L2Space
public import Mathlib.Tactic.Linarith
public import Mathlib.Tactic.Ring

/-! # Pairing estimates for real L² truncations -/

@[expose] public section
noncomputable section
open MeasureTheory
namespace HeatKernel
variable {α : Type*} [MeasurableSpace α] {μ : Measure α}

theorem inner_negativePart_eq (a b : Lp ℝ 2 μ)
    (hz : b =ᵐ[μ] fun x => max (-(a x)) 0) :
    inner ℝ a b = -‖b‖ ^ 2 := by
  calc
    _ = -inner ℝ (b) (b) := by
      rw [L2.inner_def, L2.inner_def, ← integral_neg]
      apply integral_congr_ae
      filter_upwards [hz] with x hx
      simp only [Real.inner_apply, hx]
      by_cases h : (a) x ≤ 0
      · rw [max_eq_left (neg_nonneg.mpr h)]
        ring
      · rw [max_eq_right (by linarith)]
        ring
    _ = _ := by rw [real_inner_self_eq_norm_sq]
theorem norm_sq_positiveLevel_le_pairing (a b f : Lp ℝ 2 μ)
    (hf : ∀ᵐ x ∂μ, f x ≤ 1)
    (hz : b =ᵐ[μ] fun x => max (a x - 1) 0) :
    ‖b‖ ^ 2 ≤ inner ℝ a b - inner ℝ f b := by
  have hpoint : ∀ᵐ x ∂μ,
      inner ℝ ((b) x) ((b) x) ≤
        inner ℝ ((a) x) ((b) x) -
          inner ℝ (f x) ((b) x) := by
    filter_upwards [hf, hz] with x hfx hzx
    simp only [Real.inner_apply, hzx]
    by_cases h : (a) x ≤ 1
    · rw [max_eq_right (sub_nonpos.mpr h)]
      simp only [mul_zero, sub_zero, le_refl]
    · rw [max_eq_left (by linarith)]
      nlinarith [mul_nonneg (sub_nonneg.mpr hfx)
        (show 0 ≤ (a) x - 1 by linarith)]
  rw [← real_inner_self_eq_norm_sq, L2.inner_def, L2.inner_def, L2.inner_def,
    ← integral_sub (L2.integrable_inner (𝕜 := ℝ) (a)
      (b)) (L2.integrable_inner (𝕜 := ℝ) f (b))]
  exact integral_mono_ae
    (L2.integrable_inner (𝕜 := ℝ) (b) (b))
    ((L2.integrable_inner (𝕜 := ℝ) (a) (b)).sub
      (L2.integrable_inner (𝕜 := ℝ) f (b))) hpoint

end HeatKernel

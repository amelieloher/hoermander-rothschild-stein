-- Copyright (c) 2026 Scott Armstrong and Amélie Loher. All rights reserved.
-- Released under Apache 2.0 license as described in the file LICENSE.
module

public import Mathlib.MeasureTheory.Function.L2Space
public import Mathlib.MeasureTheory.Measure.Lebesgue.Basic

/-! # Scalar integral formulas for L² pairings

Pairing with a scalar L² class agrees with integration against any of
its measurable representatives. This converts Hilbert-space weak time
identities into iterated scalar integral identities.
-/

@[expose] public section

noncomputable section

open MeasureTheory

namespace HeatKernel

/-- Pairing an L² function with a scalar L² class is the integral of their scalar product. -/
theorem inner_toLp_two_eq_integral_mul {α : Type*} [MeasurableSpace α]
    {μ : Measure α} (u : Lp ℝ 2 μ) {f : α → ℝ} (hf : MemLp f 2 μ) :
    inner ℝ u (hf.toLp f) = ∫ x, u x * f x ∂μ := by
  rw [L2.inner_def]
  apply integral_congr_ae
  filter_upwards [hf.coeFn_toLp] with x hx
  simp only [Real.inner_apply, hx]

/-- The scalar product of an L² function with an L² representative is integrable. -/
theorem integrable_mul_scalar_L2 {α : Type*} [MeasurableSpace α]
    {μ : Measure α} (u : Lp ℝ 2 μ) {f : α → ℝ} (hf : MemLp f 2 μ) :
    Integrable (fun x => u x * f x) μ := by
  apply (L2.integrable_inner (𝕜 := ℝ) u (hf.toLp f)).congr
  filter_upwards [hf.coeFn_toLp] with x hx
  simp only [Real.inner_apply, hx]

/-- A pairing with the sum of two scalar L² classes is their combined scalar integral. -/
theorem inner_add_toLp_two_eq_integral_mul_add {α : Type*} [MeasurableSpace α]
    {μ : Measure α} (u : Lp ℝ 2 μ) {f g : α → ℝ}
    (hf : MemLp f 2 μ) (hg : MemLp g 2 μ) :
    inner ℝ u (hf.toLp f + hg.toLp g) = ∫ x, u x * (f x + g x) ∂μ := by
  change inner ℝ u ((hf.add hg).toLp (f + g)) = _
  exact inner_toLp_two_eq_integral_mul u (hf.add hg)

/-- An integrated weak Hilbert-space pairing gives the corresponding iterated scalar identity. -/
theorem integral_scalar_pairing_eq_zero_of_inner_pairing {α : Type*} [MeasurableSpace α]
    {μ : Measure α} (u : ℝ → Lp ℝ 2 μ) (f g : ℝ → α → ℝ)
    (hf : ∀ t, MemLp (f t) 2 μ) (hg : ∀ t, MemLp (g t) 2 μ)
    (hweak : Integrable (fun t => inner ℝ (u t)
      ((hf t).toLp (f t) + (hg t).toLp (g t))) ∧
      (∫ t, inner ℝ (u t) ((hf t).toLp (f t) + (hg t).toLp (g t))) = 0) :
    Integrable (fun t => ∫ x, u t x * (f t x + g t x) ∂μ) ∧
      (∫ t, ∫ x, u t x * (f t x + g t x) ∂μ) = 0 := by
  simpa only [inner_add_toLp_two_eq_integral_mul_add] using hweak

end HeatKernel

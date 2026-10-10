-- Copyright (c) 2026 Scott Armstrong and Amélie Loher. All rights reserved.
-- Released under Apache 2.0 license as described in the file LICENSE.
module

public import HeatKernel.Geometry.HorizontalCurve
public import Mathlib.Topology.Algebra.Algebra.Rat

/-! Recovering a joint Euclidean gradient bound from countably many directional bounds. -/

@[expose] public section
set_option autoImplicit false
set_option relaxedAutoImplicit false
noncomputable section
open Set MeasureTheory
open scoped BigOperators
namespace HeatKernel

/-- Rational directional bounds imply the sharp joint Euclidean gradient bound. -/
theorem sqrt_sum_sq_le_of_rat_directional_bounds {q : ℕ} (g : Fin q → ℝ) {L : ℝ} (hL : 0 ≤ L)
    (h : ∀ b : Fin q → ℚ,
      |∑ i, (b i : ℝ) * g i| ≤ L * Real.sqrt (∑ i, (b i : ℝ) ^ 2)) :
    Real.sqrt (∑ i, g i ^ 2) ≤ L := by
  have hd : DenseRange (fun b : Fin q → ℚ => fun i => (b i : ℝ)) :=
    DenseRange.piMap fun _ => Rat.denseRange_cast
  have hc : IsClosed {b : Fin q → ℝ | |∑ i, b i * g i| ≤ L * Real.sqrt (∑ i, b i ^ 2)} :=
    isClosed_le
      (continuous_finsetSum _ (fun i _ => (continuous_apply i).mul continuous_const)).abs
      (continuous_const.mul (Real.continuous_sqrt.comp
        (continuous_finsetSum _ (fun i _ => (continuous_apply i).pow 2))))
  have hall : ∀ b : Fin q → ℝ, |∑ i, b i * g i| ≤ L * Real.sqrt (∑ i, b i ^ 2) :=
    fun b => isClosed_property hd hc h b
  have hs : 0 ≤ ∑ i, g i ^ 2 := Finset.sum_nonneg fun i _ => sq_nonneg (g i)
  have hb := hall g
  simp only [← pow_two] at hb
  rw [abs_of_nonneg hs] at hb
  have he := Real.sq_sqrt hs
  have hn := Real.sqrt_nonneg (∑ i, g i ^ 2)
  nlinarith

/-- Countably many almost-everywhere rational directional bounds give one sharp joint
horizontal-gradient bound on a common full-measure set. -/
theorem ae_sqrt_sum_sq_le_of_rat_directional_bounds {A : Type*} [MeasurableSpace A]
    {μ : Measure A} {q : ℕ} (g : Fin q → A → ℝ) {L : ℝ} (hL : 0 ≤ L)
    (h : ∀ b : Fin q → ℚ, ∀ᵐ x ∂μ,
      |∑ i, (b i : ℝ) * g i x| ≤ L * Real.sqrt (∑ i, (b i : ℝ) ^ 2)) :
    ∀ᵐ x ∂μ, Real.sqrt (∑ i, g i x ^ 2) ≤ L := by
  have hall := ae_all_iff.mpr h
  filter_upwards [hall] with x hx
  exact sqrt_sum_sq_le_of_rat_directional_bounds (fun i => g i x) hL hx

end HeatKernel

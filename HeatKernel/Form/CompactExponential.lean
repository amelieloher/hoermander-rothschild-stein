-- Copyright (c) 2026 Scott Armstrong and Amélie Loher. All rights reserved.
-- Released under Apache 2.0 license as described in the file LICENSE.
module

public import Mathlib.Analysis.Calculus.BumpFunction.InnerProduct
public import Mathlib.Analysis.SpecialFunctions.ExpDeriv
public import Mathlib.Analysis.Calculus.ContDiff.Deriv
import Mathlib.Tactic.Linter
import Mathlib.Tactic.Linarith

/-! # Smooth compact extensions of the exponential on bounded intervals -/

@[expose] public section

noncomputable section

open Set Filter
open scoped Topology

namespace HeatKernel

/-- On any fixed bounded interval, the exponential minus one has a smooth compact extension
vanishing at zero, with the same derivative throughout that interval. -/
theorem exists_compact_exponential (α : ℝ) {A : ℝ} (hA : 0 ≤ A) :
    ∃ η : ℝ → ℝ, ContDiff ℝ (⊤ : ℕ∞) η ∧ HasCompactSupport η ∧ η 0 = 0 ∧
      ∀ s, ‖s‖ ≤ A → η s = Real.exp (α * s) - 1 ∧ deriv η s = α * Real.exp (α * s) := by
  let χ : ContDiffBump (0 : ℝ) :=
    { rIn := A + 1
      rOut := A + 2
      rIn_pos := by linarith
      rIn_lt_rOut := by linarith }
  let η : ℝ → ℝ := fun s => (Real.exp (α * s) - 1) * χ s
  have hη : ContDiff ℝ (⊤ : ℕ∞) η :=
    (((contDiff_const.mul contDiff_id).exp).sub contDiff_const).mul χ.contDiff
  refine ⟨η, hη, χ.hasCompactSupport.mul_left, by simp [η], fun s hs => ?_⟩
  have hball : s ∈ Metric.ball (0 : ℝ) χ.rIn := by
    simpa only [Metric.mem_ball, dist_zero_right, χ] using (lt_of_le_of_lt hs (by linarith : A < A + 1))
  have he : η =ᶠ[𝓝 s] (fun t => Real.exp (α * t) - 1) := by
    filter_upwards [χ.eventuallyEq_one_of_mem_ball hball] with t ht
    simp only [η, ht, Pi.one_apply, mul_one]
  refine ⟨he.eq_of_nhds, ?_⟩
  rw [he.deriv_eq]
  have H := (((hasDerivAt_id s).const_mul α).exp).sub_const 1
  simpa only [id_eq, mul_one, mul_comm] using H.deriv


end HeatKernel

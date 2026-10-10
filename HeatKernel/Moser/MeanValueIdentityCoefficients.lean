-- Copyright (c) 2026 Scott Armstrong and Amélie Loher. All rights reserved.
-- Released under Apache 2.0 license as described in the file LICENSE.
module

public import HeatKernel.Moser.MeanValueNonnegativeCylinder
import Mathlib.Tactic

/-! # Identity-coefficient ellipticity -/

@[expose] public section
set_option autoImplicit false
set_option relaxedAutoImplicit false
noncomputable section
open Set MeasureTheory TopologicalSpace RothschildStein
open scoped ENNReal
namespace HeatKernel

/-- The identity matrix is symmetric and has both ellipticity constants equal to one. -/
theorem identity_coefficients_ellipticity (N q : ℕ) :
    ∀ᵐ _z : ℝ × (Fin N → ℝ) ∂volume,
      (∀ i j : Fin q, (if i = j then (1 : ℝ) else 0) = if j = i then 1 else 0) ∧
      ∀ ξ : Fin q → ℝ,
        1 * ∑ i, ξ i ^ 2 ≤ ∑ i, ∑ j, (if i = j then (1 : ℝ) else 0) * ξ i * ξ j ∧
        (∑ i, ∑ j, (if i = j then (1 : ℝ) else 0) * ξ i * ξ j) ≤ 1 * ∑ i, ξ i ^ 2 := by
  classical
  apply Filter.Eventually.of_forall
  intro z
  refine ⟨fun i j => by simp only [eq_comm], fun ξ => ?_⟩
  simp [ite_mul, pow_two]

end HeatKernel

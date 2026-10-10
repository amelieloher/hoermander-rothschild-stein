-- Copyright (c) 2026 Scott Armstrong and Amélie Loher. All rights reserved.
-- Released under Apache 2.0 license as described in the file LICENSE.
module

public import Mathlib.Analysis.Normed.Operator.ContinuousLinearMap
public import Mathlib.Analysis.Complex.Basic

/-! # Complex operator identification on a real subspace

Complex-linear maps agreeing on a real subspace agree everywhere when
every vector has a real and imaginary decomposition in that subspace.
-/

@[expose] public section

namespace HeatKernel

/-- Agreement on a real subspace with full real-imaginary decomposition identifies complex-linear maps. -/
theorem complexLinearMap_eq_of_real_decomposition {H E F : Type*}
    [NormedAddCommGroup H] [NormedSpace ℝ H]
    [NormedAddCommGroup E] [NormedSpace ℂ E]
    [NormedAddCommGroup F] [NormedSpace ℂ F]
    (j : H →L[ℝ] E) (hspan : ∀ z : E, ∃ a b : H, z = j a + Complex.I • j b)
    (A B : E →L[ℂ] F) (hreal : ∀ v, A (j v) = B (j v)) : A = B := by
  ext z
  obtain ⟨a, b, rfl⟩ := hspan z
  rw [map_add, map_add, map_smul, map_smul, hreal, hreal]

end HeatKernel

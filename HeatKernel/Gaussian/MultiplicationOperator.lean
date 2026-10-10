-- Copyright (c) 2026 Scott Armstrong and Amélie Loher. All rights reserved.
-- Released under Apache 2.0 license as described in the file LICENSE.
module

public import Mathlib.MeasureTheory.Function.Holder
public import Mathlib.Analysis.Normed.Operator.Mul
import Mathlib.Tactic

/-! # Bounded multiplication on the real square-integrable space

Essentially bounded scalar functions define continuous multiplication operators
on the real square-integrable space. Reciprocal functions give inverse operators.
-/

@[expose] public section
set_option autoImplicit false
set_option relaxedAutoImplicit false
noncomputable section
open MeasureTheory
namespace HeatKernel.Gaussian

/-- Multiplication by an essentially bounded real function on the real L² space. -/
def l2Multiplication {α : Type*} [MeasurableSpace α] {μ : Measure α}
    (m : Lp ℝ ⊤ μ) : Lp ℝ 2 μ →L[ℝ] Lp ℝ 2 μ :=
  (ContinuousLinearMap.mul ℝ ℝ).holderL μ ⊤ 2 2 m

/-- The multiplication operator has the expected almost everywhere representative. -/
theorem coeFn_l2Multiplication {α : Type*} [MeasurableSpace α] {μ : Measure α}
    (m : Lp ℝ ⊤ μ) (f : Lp ℝ 2 μ) :
    l2Multiplication m f =ᵐ[μ] fun x ↦ m x * f x :=
  (ContinuousLinearMap.mul ℝ ℝ).coeFn_holder m f

/-- Reciprocal multipliers yield an identity composition on L². -/
theorem l2Multiplication_comp_eq_id {α : Type*} [MeasurableSpace α] {μ : Measure α}
    (m n : Lp ℝ ⊤ μ) (hmn : ∀ᵐ x ∂μ, m x * n x = 1) :
    (l2Multiplication m).comp (l2Multiplication n) = ContinuousLinearMap.id ℝ (Lp ℝ 2 μ) := by
  ext f
  filter_upwards [coeFn_l2Multiplication m (l2Multiplication n f),
    coeFn_l2Multiplication n f, hmn] with x hx hy hz
  change (l2Multiplication m (l2Multiplication n f)) x = f x
  rw [hx, hy, ← mul_assoc, hz, one_mul]

end HeatKernel.Gaussian

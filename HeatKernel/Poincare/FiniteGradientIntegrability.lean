-- Copyright (c) 2026 Scott Armstrong and Amélie Loher. All rights reserved.
-- Released under Apache 2.0 license as described in the file LICENSE.
module

public import HeatKernel.Poincare.FiniteGradientLength

set_option autoImplicit false
set_option relaxedAutoImplicit false
@[expose] public section
noncomputable section
open Set Filter MeasureTheory
open scoped ENNReal BigOperators
namespace HeatKernel

/-- The Euclidean length of finitely many Lp components is itself in Lp. -/
theorem memLp_finite_gradient_length
    {A : Type*} [MeasurableSpace A] {μ : Measure A} {q : ℕ} {p : ℝ≥0∞}
    {g : Fin q → A → ℝ} (hg : ∀ j, MemLp (g j) p μ) :
    MemLp (fun x => Real.sqrt (∑ j, g j x ^ 2)) p μ := by
  have hsum : MemLp (fun x => ∑ j, ‖g j x‖) p μ :=
    memLp_finsetSum Finset.univ (fun j _ => (hg j).norm)
  apply hsum.mono' (aestronglyMeasurable_sqrt_sum_sq (fun j => (hg j).aestronglyMeasurable))
  apply Eventually.of_forall
  intro x
  have hh := abs_sqrt_sum_sq_sub_le_sum_abs (fun j => g j x) (fun _ => 0)
  simpa only [Real.norm_eq_abs, sub_zero, zero_pow (by norm_num : (2 : ℕ) ≠ 0),
    Finset.sum_const_zero, Real.sqrt_zero] using hh

end HeatKernel

-- Copyright (c) 2026 Scott Armstrong and Amélie Loher. All rights reserved.
-- Released under Apache 2.0 license as described in the file LICENSE.
module

public import HeatKernel.Moser.MeanValueEssentialBound
public import HeatKernel.Moser.MeanValueIterationConstants
import Mathlib.Tactic

/-! # Essential mean-value bounds from geometric norm recurrences -/

@[expose] public section
set_option autoImplicit false
set_option relaxedAutoImplicit false
open MeasureTheory Filter
open scoped ENNReal Topology
namespace HeatKernel

/-- A geometric norm recurrence gives an essential bound on the common inner domain.
The norm comparison and one-step energy recurrence are explicit hypotheses. -/
theorem eLpNormEssSup_le_of_geometric_norm_iteration
    {α : Type*} [MeasurableSpace α] (μ : Measure α) {f : α → ℝ}
    {p Y : ℕ → ℝ} {ρ a b : ℝ} (hp : ∀ j, 0 < p j)
    (hptop : Tendsto p atTop atTop)
    (hρ : 0 ≤ ρ) (hρone : ρ < 1) (ha : 0 ≤ a) (hb : 0 ≤ b)
    (hY : 0 ≤ Y 0)
    (hnorm : ∀ j, eLpNorm f (ENNReal.ofReal (p j)) μ ≤ ENNReal.ofReal (Y j))
    (hstep : ∀ j, Y (j + 1) ≤ Real.exp ((a + b * (j : ℝ)) * ρ ^ j) * Y j) :
    eLpNormEssSup f μ ≤
      ENNReal.ofReal (Real.exp (a * (1 - ρ)⁻¹ + b * (ρ / (1 - ρ) ^ 2)) * Y 0) := by
  apply eLpNormEssSup_le_of_unbounded_exponents μ hp hptop
  intro j
  exact (hnorm j).trans (ENNReal.ofReal_le_ofReal
    (le_exp_explicit_cost_mul_of_iteration hρ hρone ha hb hY hstep j))

end HeatKernel

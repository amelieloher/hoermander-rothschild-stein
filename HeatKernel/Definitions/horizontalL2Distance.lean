-- Copyright (c) 2026 Scott Armstrong and Amélie Loher. All rights reserved.
-- Released under Apache 2.0 license as described in the file LICENSE.
module

public import Mathlib

@[expose] public section

set_option autoImplicit false
set_option relaxedAutoImplicit false

noncomputable section

open Set MeasureTheory TopologicalSpace Filter
open scoped BigOperators Topology ENNReal NNReal

namespace HeatKernel

/-- The horizontal `ℓ²`-control distance of the fields `X₁, …, X_q`:
the infimum, in `[0, ∞]`, of the lengths `∫₀¹ |a(t)|₂ dt` of horizontal competitors from `x` to `y`,
that is, absolutely continuous curves `γ : [0, 1] → ℝᴺ` with `γ 0 = x`, `γ 1 = y` and
`γ' = ∑ᵢ aᵢ Xᵢ(γ)` almost everywhere, for almost-everywhere measurable controls `a` with integrable
Euclidean norm. It is `∞` when there is no competitor. -/
def horizontalL2Distance {N q : ℕ}
    (X : Fin q → (Fin N → ℝ) → (Fin N → ℝ))
    (x y : Fin N → ℝ) : ℝ≥0∞ :=
  sInf {r : ℝ≥0∞ | ∃ (γ : ℝ → (Fin N → ℝ)) (a : Fin q → ℝ → ℝ),
    AbsolutelyContinuousOnInterval γ 0 1 ∧
    γ 0 = x ∧ γ 1 = y ∧
    (∀ i, AEMeasurable (a i) (volume.restrict (Icc (0 : ℝ) 1))) ∧
    IntegrableOn (fun t => Real.sqrt (∑ i, a i t ^ 2)) (Icc (0 : ℝ) 1) ∧
    (∀ᵐ t ∂(volume.restrict (Icc (0 : ℝ) 1)),
      HasDerivAt γ (∑ i, a i t • X i (γ t)) t) ∧
    r = ENNReal.ofReal (∫ t in Icc (0 : ℝ) 1, Real.sqrt (∑ i, a i t ^ 2))}

end HeatKernel

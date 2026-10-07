-- Copyright (c) 2026 Scott Armstrong and Amélie Loher. All rights reserved.
-- Released under Apache 2.0 license as described in the file LICENSE.
module

public import Hormander.B.Multipliers
public import Hormander.D.Defs

@[expose] public section

noncomputable section

open scoped FourierTransform

namespace Hormander.B

variable {N : ℕ}

/-- The separated tail `(1 - φ) Λ^σ (ψ ·)` on Schwartz functions. -/
def offDiagonalTailOperator (φ ψ : SchwartzMap (Carrier N) ℝ) (σ : ℝ) : Operator N :=
  (LinearMap.id - realMultiplierOperator φ).comp
    ((lambdaOperator σ).comp (realMultiplierOperator ψ))

/-- The shared tail operator spells out the cutoff and Bessel multiplier formula. -/
theorem offDiagonalTailOperator_apply (φ ψ : SchwartzMap (Carrier N) ℝ) (σ : ℝ)
    (u : TestFunction N) (x : Carrier N) :
    offDiagonalTailOperator φ ψ σ u x =
      ((1 - φ x : ℝ) : ℂ) * lambdaOperator σ (realMultiplierOperator ψ u) x := by
  simp [offDiagonalTailOperator, realMultiplierOperator, multiplierOperator_apply,
    complexifyRealSchwartz_apply]
  ring

end Hormander.B

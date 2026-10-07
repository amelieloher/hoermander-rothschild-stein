-- Copyright (c) 2026 Scott Armstrong and Amélie Loher. All rights reserved.
-- Released under Apache 2.0 license as described in the file LICENSE.
module

public import RothschildStein.H2.LocDoubling
public import Mathlib.MeasureTheory.Function.LpSpace.Complete
public import Mathlib.MeasureTheory.Integral.Bochner.Set

@[expose] public section
set_option autoImplicit false
set_option relaxedAutoImplicit false
noncomputable section
open Set MeasureTheory Metric
open scoped ENNReal

namespace RothschildStein.H2
variable {X : Type*} [MetricSpace X] [MeasurableSpace X] [BorelSpace X]

/-- Exact off-diagonal property (OS) for an L² operator.
Centres range over Ω₁, including outside U; integrability records absolute
convergence of the Bochner integral (BB pp. 318–321). -/
def OffDiagonalL2 (D : LocDoubling X) (U : Set X) (K : X → X → ℝ)
    (T : Lp ℝ 2 (D.μ.restrict U) →L[ℝ] Lp ℝ 2 (D.μ.restrict U)) : Prop :=
  ∀ z ∈ D.Ω₁, ∀ r : ℝ, 0 < r → r ≤ D.κ / 5 →
    ∀ v : Lp ℝ 2 (D.μ.restrict U),
      (∀ᵐ x ∂D.μ.restrict U, x ∉ ball z r → v x = 0) →
      ∀ᵐ y ∂D.μ.restrict U, y ∉ ball z (4 * r) →
        IntegrableOn (fun x => K y x * v x) U D.μ ∧
        (T v) y = ∫ x in U, K y x * v x ∂D.μ

end RothschildStein.H2

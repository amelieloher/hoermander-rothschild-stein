-- Copyright (c) 2026 Scott Armstrong and Amélie Loher. All rights reserved.
-- Released under Apache 2.0 license as described in the file LICENSE.
module

public import RothschildStein.H2.OffDiagonalL2
public import RothschildStein.H2.KernelClass

@[expose] public section
set_option autoImplicit false
set_option relaxedAutoImplicit false
noncomputable section
open Set MeasureTheory Metric

namespace RothschildStein.H2
variable {X : Type*} [MetricSpace X] [MeasurableSpace X] [BorelSpace X]

/-- The analytic certificate for the weak-type and Lᵖ bounds.
Kernel smoothness is required on the transpose; the separate certificate
for the adjoint exchanges the kernel variables. -/
structure LocalL2Certificate (D : LocDoubling X) (xbar : X) (R β A S cT : ℝ)
    (K : X → X → ℝ)
    (T : Lp ℝ 2 (D.μ.restrict (ball xbar R)) →L[ℝ]
      Lp ℝ 2 (D.μ.restrict (ball xbar R))) : Prop where
  norm_le : ‖T‖ ≤ cT
  offDiagonal : OffDiagonalL2 D (ball xbar R) K T
  kernel_transpose : KernelClass D.μ D.Ω₁ β 0 A S (fun x y => K y x)
  measurable_kernel : Measurable (Function.uncurry K)
  support : ∀ x y, x ∉ ball xbar R ∨ y ∉ ball xbar R → K x y = 0

end RothschildStein.H2

-- Copyright (c) 2026 Scott Armstrong and Amélie Loher. All rights reserved.
-- Released under Apache 2.0 license as described in the file LICENSE.
module

public import HeatKernel.Kernel.KernelLocalIntegrability
public import HeatKernel.Kernel.CoordinateMeasure

/-! # Local integrability in two-space kernel coordinates

The measure-preserving coordinate equivalence transports the kernel's positive
spacetime local integrability to the Euclidean domain of the heat operator.
-/

@[expose] public section

noncomputable section

open MeasureTheory

namespace HeatKernel

variable {n : ℕ}
    (T : ℝ → Lp ℝ 2 (volume : Measure (Fin n → ℝ)) →L[ℝ]
      Lp ℝ 2 (volume : Measure (Fin n → ℝ)))
    (u : ℝ → Lp ℝ 2 (volume : Measure (Fin n → ℝ)) → (Fin n → ℝ) → ℝ)
    (hu : ∀ t, 0 < t → ∀ f, Continuous (u t f))
    (hae : ∀ t, 0 < t → ∀ f, T t f =ᵐ[volume] u t f)
    (hjoint : ∀ f, ContinuousOn (fun p : ℝ × (Fin n → ℝ) => u p.1 f p.2)
      {p | 0 < p.1})

include hjoint

/-- The coordinate kernel is locally integrable on the positive-time Euclidean domain. -/
theorem locallyIntegrableOn_coordinate_heatRepresentativeKernel :
    LocallyIntegrableOn (fun z : Fin (1 + (n + n)) → ℝ =>
      evaluationKernel (heatRepresentativeEvaluation T u hu hae)
        (timeTwoSpaceCoordinates n z).1 (timeTwoSpaceCoordinates n z).2.1
        (timeTwoSpaceCoordinates n z).2.2) {z | 0 < z 0} volume := by
  exact locallyIntegrableOn_comp_timeTwoSpaceCoordinates n
    (isOpen_lt continuous_const continuous_fst)
    (locallyIntegrableOn_heatRepresentativeKernel T u hu hae hjoint)

end HeatKernel

-- Copyright (c) 2026 Scott Armstrong and Amélie Loher. All rights reserved.
-- Released under Apache 2.0 license as described in the file LICENSE.
module

public import HeatKernel.Kernel.TwoSpaceHeatAdjoint
public import Hormander.Interface
public import Mathlib.MeasureTheory.Measure.OpenPos

/-! # Smooth representatives for the two spatial heat operators

The spacetime adjoint identity converts a weak heat-test identity into the weak
Hörmander equation. Hypoellipticity and full support give a unique smooth representative.
-/

@[expose] public section

noncomputable section

open MeasureTheory
open scoped BigOperators

namespace HeatKernel

open Hormander.Interface RothschildStein

/-- A locally integrable two-space heat-test solution satisfies the spacetime Hörmander equation. -/
theorem hasWeakHormanderEquation_horizontalTwoSpaceHeatFields_of_integral_identity {n q : ℕ}
    (G : HomogeneousGroup n) (hq : q ≤ n) (u : (Fin (1 + (n + n)) → ℝ) → ℝ)
    (hu : LocallyIntegrableOn u {x | 0 < x 0} volume)
    (hweak : ∀ φ : (Fin (1 + (n + n)) → ℝ) → ℝ,
      ContDiff ℝ (⊤ : ℕ∞) φ → HasCompactSupport φ → tsupport φ ⊆ {x | 0 < x 0} →
      (∫ x in {x | 0 < x 0}, u x *
        (2 * fderiv ℝ φ x (leftCoordinateInclusion 1 (n + n) (fun _ => 1)) +
          ∑ i : Fin (q + q), fderiv ℝ
            (fun y => fderiv ℝ φ y
              (liftRightField 1 (sumFields (G.horizontalFields hq) (G.horizontalFields hq) i) y)) x
            (liftRightField 1 (sumFields (G.horizontalFields hq) (G.horizontalFields hq) i) x))) = 0) :
    HasWeakHormanderEquation {x | 0 < x 0} (horizontalTwoSpaceHeatFields G hq) 0 0 u := by
  refine ⟨hu, contDiffOn_const, ?_⟩
  intro φ hφ hcompact hsupp
  simpa only [hormanderAdjointTest_horizontalTwoSpaceHeatFields G hq φ hφ, Pi.zero_apply,
    MulZeroClass.zero_mul, integral_zero] using hweak φ hφ hcompact hsupp

end HeatKernel

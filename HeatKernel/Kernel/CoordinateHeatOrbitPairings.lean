-- Copyright (c) 2026 Scott Armstrong and Amélie Loher. All rights reserved.
-- Released under Apache 2.0 license as described in the file LICENSE.
module

public import HeatKernel.Kernel.SmoothSpacetimeOrbitTests
public import HeatKernel.Kernel.L2ScalarPairings
public import Mathlib.MeasureTheory.Integral.Prod
public import HeatKernel.Kernel.CoordinateTestSlices
public import HeatKernel.Kernel.InverseCoordinateMeasure
public import HeatKernel.Kernel.CompactSumSquaresTests
public import HeatKernel.Kernel.SpacetimeRank

/-! # Weak coordinate heat identities from generator pairings

The literal lifted horizontal sum of squares preserves smooth compact
tests. Pairing the orbit generator against those tests yields the
coordinate adjoint heat identity.
-/

@[expose] public section

noncomputable section

open MeasureTheory TopologicalSpace RothschildStein

namespace HeatKernel

/-- Lifted horizontal sums of squares of compact coordinate tests have L² spatial slices. -/
theorem memLp_two_lifted_sumSquares_test_slice {n q : ℕ}
    (X : Fin q → (Fin n → ℝ) → Fin n → ℝ)
    (hX : ∀ i, ContDiff ℝ (⊤ : ℕ∞) (X i))
    (φ : (Fin (1 + n) → ℝ) → ℝ) (hφ : ContDiff ℝ (⊤ : ℕ∞) φ)
    (hc : HasCompactSupport φ) (t : ℝ) :
    MemLp (fun x => sumSquares (fun i => liftRightField 1 (X i)) φ
      ((timeSpaceCoordinates n).symm (t, x))) 2 volume :=
  memLp_two_coordinate_test_slice _
    (contDiff_sumSquares_of_contDiff _ (fun i => (hX i).liftRightField 1) φ hφ)
    (hasCompactSupport_sumSquares _ φ hc) t

end HeatKernel

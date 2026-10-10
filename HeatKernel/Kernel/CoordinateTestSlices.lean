-- Copyright (c) 2026 Scott Armstrong and Amélie Loher. All rights reserved.
-- Released under Apache 2.0 license as described in the file LICENSE.
module

public import HeatKernel.Kernel.SmoothSpacetimeDifferentiation
public import HeatKernel.Kernel.CoordinateDerivatives

/-! # Compact coordinate tests as L² slice curves

The time-space coordinate equivalence transports smooth compact tests
and identifies their scalar time derivative with the first coordinate
differential.
-/

@[expose] public section

noncomputable section

open MeasureTheory
open RothschildStein

namespace HeatKernel

/-- Pulling a smooth coordinate test back to time and space preserves smoothness and compact support. -/
theorem smooth_compact_inverse_timeSpace_test {n : ℕ}
    (φ : (Fin (1 + n) → ℝ) → ℝ) (hφ : ContDiff ℝ (⊤ : ℕ∞) φ)
    (hc : HasCompactSupport φ) :
    ContDiff ℝ (⊤ : ℕ∞) (φ ∘ (timeSpaceCoordinates n).symm) ∧
      HasCompactSupport (φ ∘ (timeSpaceCoordinates n).symm) :=
  ⟨hφ.comp (timeSpaceCoordinates n).symm.contDiff,
    hc.comp_isClosedEmbedding (timeSpaceCoordinates n).symm.toHomeomorph.isClosedEmbedding⟩

/-- A smooth compact coordinate test has an L² spatial slice at every time. -/
theorem memLp_two_coordinate_test_slice {n : ℕ}
    (φ : (Fin (1 + n) → ℝ) → ℝ) (hφ : ContDiff ℝ (⊤ : ℕ∞) φ)
    (hc : HasCompactSupport φ) (t : ℝ) :
    MemLp (fun x => φ ((timeSpaceCoordinates n).symm (t, x))) 2 volume := by
  obtain ⟨hC, hcompact⟩ := smooth_compact_inverse_timeSpace_test φ hφ hc
  exact memLp_two_spatial_slice (φ ∘ (timeSpaceCoordinates n).symm) hC.continuous hcompact t

/-- The differential in the product time direction is the first coordinate differential. -/
theorem fderiv_inverse_timeSpace_test_time {n : ℕ}
    (φ : (Fin (1 + n) → ℝ) → ℝ) (p : ℝ × (Fin n → ℝ))
    (hφ : DifferentiableAt ℝ φ ((timeSpaceCoordinates n).symm p)) :
    fderiv ℝ (φ ∘ (timeSpaceCoordinates n).symm) p (1, 0) =
      fderiv ℝ φ ((timeSpaceCoordinates n).symm p)
        (leftCoordinateInclusion 1 n (fun _ => 1)) := by
  have h := hφ.hasFDerivAt.comp p (timeSpaceCoordinates n).symm.hasFDerivAt
  have heq := congrArg (fun L : (ℝ × (Fin n → ℝ)) →L[ℝ] ℝ => L (1, 0)) h.fderiv
  simpa only [ContinuousLinearMap.comp_apply, ContinuousLinearEquiv.coe_coe,
    timeSpaceCoordinates_symm_one_zero] using heq

end HeatKernel

-- Copyright (c) 2026 Scott Armstrong and Amélie Loher. All rights reserved.
-- Released under Apache 2.0 license as described in the file LICENSE.
module

public import HeatKernel.Semigroup.InverseResolventGraph

/-! # Operator graphs under real Hilbert isometries -/

@[expose] public section

noncomputable section

namespace HeatKernel

variable {H K : Type*} [NormedAddCommGroup H] [InnerProductSpace ℝ H]
    [NormedAddCommGroup K] [InnerProductSpace ℝ K]

/-- Conjugation by a real Hilbert isometry transports the inverse-resolvent graph. -/
theorem inverseResolventGraph_conjugate_isometry (e : H ≃ₗᵢ[ℝ] K) (R : H →L[ℝ] H)
    (u g : H) :
    InverseResolventGraph
      (e.toContinuousLinearEquiv.toContinuousLinearMap.comp
        (R.comp e.symm.toContinuousLinearEquiv.toContinuousLinearMap)) (e u) (e g) ↔
      InverseResolventGraph R u g := by
  rw [inverseResolventGraph_iff, inverseResolventGraph_iff]
  change e (R (e.symm (e u + e g))) = e u ↔ R (u + g) = u
  rw [← map_add, e.symm_apply_apply]
  exact e.injective.eq_iff

end HeatKernel

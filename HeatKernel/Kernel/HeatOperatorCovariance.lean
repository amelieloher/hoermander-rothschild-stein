-- Copyright (c) 2026 Scott Armstrong and Amélie Loher. All rights reserved.
-- Released under Apache 2.0 license as described in the file LICENSE.
module

public import HeatKernel.Kernel.DilationCovariance
public import HeatKernel.Semigroup.BoundedHeatOperators

/-! # Covariance of the bounded-resolvent heat operators

Resolvent conjugation identities transport to the heat operators, including at time zero.
-/

@[expose] public section

noncomputable section

open scoped NNReal

namespace HeatKernel

variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]

/-- Unitary resolvent rescaling gives covariance of heat operators at every nonnegative time. -/
theorem conjStarAlgEquiv_heatOperator_of_resolvent_scale (e : H ≃ₗᵢ[ℂ] H)
    (R : H →L[ℂ] H) (hR : IsSelfAdjoint R)
    (hσ : spectrum ℝ R ⊆ Set.Icc (0 : ℝ) 1)
    {scale : ℝ≥0} (hscale : 0 < scale)
    (he : e.symm.conjStarAlgEquiv R = cfc (resolventMultiplier scale) R) (t : ℝ≥0) :
    e.symm.conjStarAlgEquiv (heatOperator R t) = heatOperator R (scale * t) := by
  by_cases ht : t = 0
  · subst t
    simp only [mul_zero, heatOperator_zero R hR, map_one]
  have ht' : 0 < t := pos_iff_ne_zero.mpr ht
  have hst : 0 < scale * t := mul_pos hscale ht'
  have hfun (u : ℝ≥0) (hu : 0 < u) : semigroupMultiplier u = heatMultiplier (u : ℝ) :=
    funext (semigroupMultiplier_of_pos hu)
  unfold heatOperator
  rw [hfun t ht', hfun (scale * t) hst]
  change e.symm.conjStarAlgEquiv
    (cfc (fun s : ℝ => Real.exp (t : ℝ) * expNegInvGlue (s / (t : ℝ))) R) =
    cfc (fun s : ℝ => Real.exp ((scale * t : ℝ≥0) : ℝ) *
      expNegInvGlue (s / ((scale * t : ℝ≥0) : ℝ))) R
  simpa only [NNReal.coe_mul] using
    conjStarAlgEquiv_heat_of_resolvent e R hR hσ (NNReal.coe_pos.mpr hscale)
      (NNReal.coe_pos.mpr ht') he

end HeatKernel

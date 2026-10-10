-- Copyright (c) 2026 Scott Armstrong and Amélie Loher. All rights reserved.
-- Released under Apache 2.0 license as described in the file LICENSE.
module

public import HeatKernel.Kernel.FunctionalCalculusCovariance
public import Mathlib.Analysis.SpecialFunctions.SmoothTransition

/-! # Dilation covariance through the bounded resolvent

The rational change of resolvent parameter turns dilation of the operator into rescaling
of time in the heat multiplier. The identity holds at the endpoint zero as well.
-/

@[expose] public section

noncomputable section

namespace HeatKernel

/-- Composing the continuous heat function with the rational resolvent parameter rescales time. -/
theorem expNegInvGlue_resolventParameter {scale t s : ℝ} (hscale : 0 < scale)
    (ht : 0 < t) (hs : s ∈ Set.Icc (0 : ℝ) 1) :
    Real.exp t * expNegInvGlue ((s / (s + scale * (1 - s))) / t) =
      Real.exp (scale * t) * expNegInvGlue (s / (scale * t)) := by
  rcases eq_or_lt_of_le hs.1 with h | h
  · simp [← h]
  have hd : 0 < s + scale * (1 - s) := by
    exact add_pos_of_pos_of_nonneg h (mul_nonneg hscale.le (sub_nonneg.mpr hs.2))
  have hg := div_pos (div_pos h hd) ht
  have hst := div_pos h (mul_pos hscale ht)
  rw [expNegInvGlue, ite_eq_right (not_le.mpr hg), expNegInvGlue,
    ite_eq_right (not_le.mpr hst), ← Real.exp_add, ← Real.exp_add]
  congr 1
  simp only [inv_div]
  field_simp
  ring

variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]

/-- Resolvent conjugacy implies heat-semigroup conjugacy with the rescaled time. -/
theorem conjStarAlgEquiv_heat_of_resolvent (e : H ≃ₗᵢ[ℂ] H) (A : H →L[ℂ] H)
    (hA : IsSelfAdjoint A) (hσ : spectrum ℝ A ⊆ Set.Icc (0 : ℝ) 1)
    {scale t : ℝ} (hscale : 0 < scale) (ht : 0 < t)
    (he : e.symm.conjStarAlgEquiv A = cfc (fun s : ℝ => s / (s + scale * (1 - s))) A) :
    e.symm.conjStarAlgEquiv (cfc (fun s : ℝ => Real.exp t * expNegInvGlue (s / t)) A) =
      cfc (fun s : ℝ => Real.exp (scale * t) * expNegInvGlue (s / (scale * t))) A := by
  have hf : Continuous (fun s : ℝ => Real.exp t * expNegInvGlue (s / t)) :=
    continuous_const.mul ((expNegInvGlue.contDiff (n := 0)).continuous.comp
      (continuous_id.div_const t))
  have hg : ContinuousOn (fun s : ℝ => s / (s + scale * (1 - s))) (spectrum ℝ A) := by
    apply continuousOn_id.div (continuousOn_id.add
      (continuousOn_const.mul (continuousOn_const.sub continuousOn_id)))
    intro s hs
    have hs' := hσ hs
    have hd : 0 < s + scale * (1 - s) := by
      rcases eq_or_lt_of_le hs'.1 with h | h
      · simp [← h, hscale]
      exact add_pos_of_pos_of_nonneg h (mul_nonneg hscale.le (sub_nonneg.mpr hs'.2))
    exact ne_of_gt hd
  apply conjStarAlgEquiv_cfc_eq_of_comp e.symm A hA _ _ _ hf hg he
  intro s hs
  exact expNegInvGlue_resolventParameter hscale ht (hσ hs)

end HeatKernel

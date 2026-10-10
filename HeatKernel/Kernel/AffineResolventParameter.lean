-- Copyright (c) 2026 Scott Armstrong and Amélie Loher. All rights reserved.
-- Released under Apache 2.0 license as described in the file LICENSE.
module

public import HeatKernel.Kernel.FunctionalCalculusCovariance

/-! # The affine resolvent parameter and its inverse

A positive scale makes the affine parameter strictly positive on the
resolvent spectrum. Continuous functional calculus gives its bounded
right inverse and the rational parameter for the scaled resolvent.
-/

@[expose] public section

noncomputable section

namespace HeatKernel

/-- The affine resolvent parameter is strictly positive on the unit interval. -/
theorem affine_resolvent_parameter_pos {c s : ℝ} (hc : 0 < c) (hs : s ∈ Set.Icc (0 : ℝ) 1) :
    0 < c + (1 - c) * s := by
  have heq : c + (1 - c) * s = s + c * (1 - s) := by ring
  rw [heq]
  rcases eq_or_lt_of_le hs.1 with hz | hp
  · simpa only [← hz, sub_zero, mul_one, zero_add] using hc
  · exact add_pos_of_pos_of_nonneg hp (mul_nonneg hc.le (sub_nonneg.mpr hs.2))

/-- The reciprocal affine parameter is continuous on the unit interval. -/
theorem continuousOn_inverse_affine_resolvent_parameter {c : ℝ} (hc : 0 < c) :
    ContinuousOn (fun s : ℝ => (c + (1 - c) * s)⁻¹) (Set.Icc (0 : ℝ) 1) := by
  exact (continuousOn_const.add (continuousOn_const.mul continuousOn_id)).inv₀
    (fun s hs => ne_of_gt (affine_resolvent_parameter_pos hc hs))

variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]

/-- The affine scalar parameter represents the corresponding affine operator. -/
theorem cfc_affine_resolvent_parameter (A : H →L[ℂ] H) (hA : IsSelfAdjoint A) (c : ℝ) :
    cfc (fun s : ℝ => c + (1 - c) * s) A = c • (1 : H →L[ℂ] H) + (1 - c) • A := by
  rw [cfc_const_add c (fun s : ℝ => (1 - c) * s) A
    (continuous_const.mul continuous_id).continuousOn hA,
    cfc_const_mul_id (1 - c) A hA, Algebra.algebraMap_eq_smul_one]

/-- Continuous functional calculus supplies a right inverse of the affine resolvent parameter. -/
theorem affine_resolvent_parameter_mul_cfc_inverse (A : H →L[ℂ] H)
    (hA : IsSelfAdjoint A) (hσ : spectrum ℝ A ⊆ Set.Icc (0 : ℝ) 1)
    {c : ℝ} (hc : 0 < c) :
    (c • (1 : H →L[ℂ] H) + (1 - c) • A) *
      cfc (fun s : ℝ => (c + (1 - c) * s)⁻¹) A = 1 := by
  rw [← cfc_affine_resolvent_parameter A hA c,
    ← cfc_mul (fun s : ℝ => c + (1 - c) * s)
      (fun s : ℝ => (c + (1 - c) * s)⁻¹) A
      (continuous_const.add (continuous_const.mul continuous_id)).continuousOn
      ((continuousOn_inverse_affine_resolvent_parameter hc).mono hσ)]
  calc
    _ = cfc (fun _ : ℝ => 1) A := cfc_congr fun s hs =>
      mul_inv_cancel₀ (ne_of_gt (affine_resolvent_parameter_pos hc (hσ hs)))
    _ = 1 := cfc_const_one ℝ A

/-- The scaled resolvent parameter is the original resolvent times the inverse affine parameter. -/
theorem cfc_scaled_resolvent_parameter_eq_mul_inverse (A : H →L[ℂ] H)
    (hA : IsSelfAdjoint A) (hσ : spectrum ℝ A ⊆ Set.Icc (0 : ℝ) 1)
    {c : ℝ} (hc : 0 < c) :
    cfc (fun s : ℝ => s / (s + c * (1 - s))) A =
      A * cfc (fun s : ℝ => (c + (1 - c) * s)⁻¹) A := by
  calc
    _ = cfc (fun s : ℝ => s * (c + (1 - c) * s)⁻¹) A := by
      apply cfc_congr
      intro s _
      change s / (s + c * (1 - s)) = s * (c + (1 - c) * s)⁻¹
      have heq : s + c * (1 - s) = c + (1 - c) * s := by ring
      rw [heq, div_eq_mul_inv]
    _ = cfc (fun s : ℝ => s) A *
        cfc (fun s : ℝ => (c + (1 - c) * s)⁻¹) A :=
      cfc_mul _ _ A continuousOn_id
        ((continuousOn_inverse_affine_resolvent_parameter hc).mono hσ)
    _ = _ := by rw [cfc_id' ℝ A hA]

end HeatKernel

-- Copyright (c) 2026 Scott Armstrong and Amélie Loher. All rights reserved.
-- Released under Apache 2.0 license as described in the file LICENSE.
module

public import HeatKernel.Kernel.AffineResolventParameter
public import HeatKernel.Kernel.DilationCovariance

/-! # Heat covariance from scaled operator graph covariance

The inverse-resolvent graph relation is expressed as its bounded
resolvent equation. Scaling the operator value under a unitary map
gives rational resolvent conjugacy and hence rescaling of heat time.
-/

@[expose] public section

noncomputable section

namespace HeatKernel

variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]

/-- Scaled graph covariance under a unitary map gives the rational resolvent conjugacy. -/
theorem conjStarAlgEquiv_resolvent_of_scaled_graph_map
    (e : H ≃ₗᵢ[ℂ] H) (A : H →L[ℂ] H) (hA : IsSelfAdjoint A)
    (hσ : spectrum ℝ A ⊆ Set.Icc (0 : ℝ) 1) {c : ℝ} (hc : 0 < c)
    (hmap : ∀ u g, A (u + g) = u → A (e u + c • e g) = e u) :
    e.symm.conjStarAlgEquiv A = cfc (fun s : ℝ => s / (s + c * (1 - s))) A := by
  let B : H →L[ℂ] H := c • (1 : H →L[ℂ] H) + (1 - c) • A
  let D : H →L[ℂ] H := cfc (fun s : ℝ => (c + (1 - c) * s)⁻¹) A
  have hinv : B * D = 1 := affine_resolvent_parameter_mul_cfc_inverse A hA hσ hc
  have hcov (v : H) : A (e (B v)) = e (A v) := by
    have hb : A (A v + (v - A v)) = A v := by
      congr 1
      abel
    have h := hmap (A v) (v - A v) hb
    have hes (a : ℝ) (w : H) : e (a • w) = a • e w :=
      e.toLinearEquiv.toLinearMap.map_smul_of_tower a w
    have heq : e (A v) + c • e (v - A v) = e (B v) := by
      change e (A v) + c • e (v - A v) = e (c • v + (1 - c) • A v)
      rw [map_add, hes, hes, map_sub,
        smul_sub, sub_smul, one_smul]
      abel
    rwa [heq] at h
  ext v
  change e.symm (A (e v)) = cfc (fun s : ℝ => s / (s + c * (1 - s))) A v
  rw [cfc_scaled_resolvent_parameter_eq_mul_inverse A hA hσ hc]
  change e.symm (A (e v)) = A (D v)
  have hb := congrArg (fun T : H →L[ℂ] H => T v) hinv
  change B (D v) = v at hb
  have h := hcov (D v)
  rw [hb] at h
  have he := congrArg e.symm h
  simpa only [LinearIsometryEquiv.symm_apply_apply] using he

end HeatKernel

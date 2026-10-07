-- Copyright (c) 2026 Scott Armstrong and Amélie Loher. All rights reserved.
-- Released under Apache 2.0 license as described in the file LICENSE.
module

public import RothschildStein.H3.LocalInterpolationParameters

set_option autoImplicit false
set_option relaxedAutoImplicit false
@[expose] public section
noncomputable section
namespace RothschildStein.H3

/-- The cutoff coefficient bound at every compact interpolation
scale yields the quarter-contraction recurrence with the exact loss.
This scalar helper is instantiated by the actual localized estimate. -/
theorem local_interpolation_step_of_cutoff_bound {P T F U a b C d R B γ η : ℝ}
    (hT : 0 ≤ T) (hF : 0 ≤ F) (hU : 0 ≤ U) (hb : 0 ≤ b) (_hC : 0 ≤ C)
    (hd : 0 < d) (hdR : d ≤ R) (hB1 : 1 ≤ B) (hBR : R ≤ B)
    (hBa : 2 * a ≤ B) (hγ : 1 ≤ γ) (hη : 0 < η) (hη4 : η ≤ 1 / 4)
    (hbound : ∀ ε : ℝ, 0 < ε → ε < 1 →
      P ≤ ε * (F + b / d ^ 2 * U + (2 * a / d) * T) + C * ε ^ (-γ) * U) :
    P ≤ (1 / 4) * T +
      ((b * R ^ (γ - 1) + C * B ^ γ) * η ^ (-γ) * U) / d ^ γ + η * F := by
  let ε := η * d / B
  have hB : 0 < B := by linarith
  obtain ⟨he, he1, heη, hecross⟩ := local_interpolation_scale_bounds hη hη4 hd hdR hB1 hBR hBa
  have hnear : ε * F ≤ η * F := mul_le_mul_of_nonneg_right heη hF
  have hcross : ε * (2 * a / d) * T ≤ (1 / 4) * T :=
    mul_le_mul_of_nonneg_right (hecross.trans hη4) hT
  have hlow : ε * (b / d ^ 2) ≤
      b * R ^ (γ - 1) * η ^ (-γ) * d ^ (-γ) := by
    have heq : ε * (b / d ^ 2) = (b / B) * (η / d) := by
      dsimp [ε]
      field_simp [hd.ne', hB.ne']
    rw [heq]
    calc
      _ ≤ b * (η / d) := mul_le_mul_of_nonneg_right
        (div_le_self hb hB1) (div_nonneg hη.le hd.le)
      _ ≤ b * (R ^ (γ - 1) * η ^ (-γ) * d ^ (-γ)) :=
        mul_le_mul_of_nonneg_left
          (local_interpolation_lower_order_loss hη (by linarith) hd hdR hγ) hb
      _ = _ := by ring
  have hfar : C * ε ^ (-γ) = C * B ^ γ * η ^ (-γ) * d ^ (-γ) := by
    rw [local_interpolation_scale_loss hη hd hB]
    ring
  have hh := hbound ε he he1
  have hdecomp : ε * (F + b / d ^ 2 * U + (2 * a / d) * T) + C * ε ^ (-γ) * U =
      ε * F + ε * (b / d ^ 2) * U + ε * (2 * a / d) * T + C * ε ^ (-γ) * U := by ring
  rw [hdecomp] at hh
  calc
    P ≤ ε * F + ε * (b / d ^ 2) * U + ε * (2 * a / d) * T + C * ε ^ (-γ) * U := hh
    _ ≤ η * F + (b * R ^ (γ - 1) * η ^ (-γ) * d ^ (-γ)) * U +
        (1 / 4) * T + (C * B ^ γ * η ^ (-γ) * d ^ (-γ)) * U :=
      add_le_add (add_le_add (add_le_add hnear
        (mul_le_mul_of_nonneg_right hlow hU)) hcross) (by rw [hfar])
    _ = _ := by rw [Real.rpow_neg hd.le]; ring

end RothschildStein.H3

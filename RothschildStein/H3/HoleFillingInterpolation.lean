-- Copyright (c) 2026 Scott Armstrong and Amélie Loher. All rights reserved.
-- Released under Apache 2.0 license as described in the file LICENSE.
module

public import RothschildStein.H3.HoleFilling

set_option autoImplicit false
set_option relaxedAutoImplicit false
@[expose] public section
noncomputable section
open Set
namespace RothschildStein.H3

/-- For a positive exponent the iteration constant is at
least two, so delta/c_gamma lies in the required quarter interval. -/
theorem holeFillingConstant_ge_two {β : ℝ} (hβ : 0 < β) :
    2 ≤ holeFillingConstant β := by
  obtain ⟨hτ, hτ1, _⟩ := holeFilling_ratio hβ
  have hp := Real.one_le_rpow_of_pos_of_le_one_of_nonpos
    (sub_pos.mpr hτ1) (by linarith [hτ]) (neg_nonpos.mpr hβ.le)
  have hb : 2 ≤ 2 * (1 - (2 / 3 : ℝ) ^ (1 / β)) ^ (-β) := by linarith
  exact hb.trans (by unfold holeFillingConstant; rw [ite_eq_right hβ.ne']; exact le_max_left _ _)

/-- Exact rescaling of the iteration coefficient. -/
theorem holeFilling_interpolation_power {C δ γ : ℝ} (hC : 0 < C) (hδ : 0 < δ) :
    C * (δ / C) ^ (-γ) = C ^ (1 + γ) * δ ^ (-γ) := by
  rw [Real.div_rpow hδ.le hC.le, Real.rpow_neg hC.le, div_inv_eq_mul,
    Real.rpow_add hC, Real.rpow_one]
  ring

/-- The full bounded scalar iteration step gives the final
small-parameter interpolation estimate with the exact loss exponent.
The geometric cutoff and compact interpolation application are separate
inputs to the recurrence (BB Proposition 8.56, p. 385). -/
theorem local_interpolation_of_scalar_recurrence
    {ψ : ℝ → ℝ} {T₀ T₁ γ c F U : ℝ}
    (hT₀ : 0 ≤ T₀) (hT : T₀ < T₁) (hγ : 0 < γ) (hc : 0 ≤ c)
    (hF : 0 ≤ F) (hU : 0 ≤ U) (hψ : ∀ t ∈ Icc T₀ T₁, 0 ≤ ψ t)
    (hb : ∃ M : ℝ, ∀ t ∈ Icc T₀ T₁, ψ t ≤ M)
    (hstep : ∀ η : ℝ, 0 < η → η ≤ 1 / 4 → ∀ t s : ℝ,
      T₀ ≤ t → t < s → s ≤ T₁ →
      ψ t ≤ (1 / 4) * ψ s + (c * η ^ (-γ) * U) / (s - t) ^ γ + η * F)
    {δ ρ R : ℝ} (hδ : 0 < δ) (hδ2 : δ ≤ 1 / 2)
    (hρ : T₀ ≤ ρ) (hρR : ρ < R) (hR : R ≤ T₁) :
    ψ ρ ≤ δ * F + (holeFillingConstant γ ^ (1 + γ) * c) *
      δ ^ (-γ) * (R - ρ) ^ (-γ) * U := by
  let C := holeFillingConstant γ
  have hC2 : 2 ≤ C := holeFillingConstant_ge_two hγ
  have hC : 0 < C := by linarith
  let η := δ / C
  have hη : 0 < η := div_pos hδ hC
  have hη4 : η ≤ 1 / 4 := (div_le_iff₀ hC).mpr (by linarith)
  have hh := holeFilling hT₀ hT hψ hb (by norm_num : (0 : ℝ) ≤ 1 / 4)
    (by norm_num : (1 / 4 : ℝ) < 1 / 3)
    (mul_nonneg (mul_nonneg hc (Real.rpow_nonneg hη.le _)) hU)
    (mul_nonneg hη.le hF) hγ.le (hstep η hη hη4) hρ hρR hR
  have hd : 0 < R - ρ := sub_pos.mpr hρR
  have hp := holeFilling_interpolation_power hC hδ (γ := γ)
  have hcancel : C * η = δ := by dsimp [η]; field_simp
  have he : C * ((c * η ^ (-γ) * U) / (R - ρ) ^ γ + η * F) =
      δ * F + (C ^ (1 + γ) * c) * δ ^ (-γ) * (R - ρ) ^ (-γ) * U := by
    rw [Real.rpow_neg hd.le]
    rw [mul_add, ← mul_assoc C η F, hcancel]
    have hp' : C * η ^ (-γ) = C ^ (1 + γ) * δ ^ (-γ) := hp
    calc
      _ = δ * F + (C * η ^ (-γ)) * c * U / (R - ρ) ^ γ := by ring
      _ = _ := by rw [hp']; ring
  exact hh.trans_eq he

end RothschildStein.H3

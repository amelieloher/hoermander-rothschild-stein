-- Copyright (c) 2026 Scott Armstrong and Amélie Loher. All rights reserved.
-- Released under Apache 2.0 license as described in the file LICENSE.
module

public import RothschildStein.H3.PhiPointBounds
public import RothschildStein.H3.SecondStepReweighting

set_option autoImplicit false
set_option relaxedAutoImplicit false
@[expose] public section
noncomputable section
namespace RothschildStein.H3
open Set
open scoped ENNReal

/-- The midpoint second-norm cutoff estimate gives the weighted
supremum bound with the stated coefficients. Only finiteness of the zero
and first Phi terms is needed. -/
theorem second_phi_bound_of_midpoint_step (N₀ N₁ N₂ : ℝ → ℝ)
    {r C a b F : ℝ} (hr : 0 < r) (hC : 0 ≤ C) (ha : 0 ≤ a)
    (hb : 0 ≤ b) (hF : 0 ≤ F)
    (hP₀ : phi (Ioo (1/2 : ℝ) 1) r 0 N₀ ≠ ⊤)
    (hP₁ : phi (Ioo (1/2 : ℝ) 1) r 1 N₁ ≠ ⊤)
    (hstep : ∀ σ ∈ Ioo (1/2 : ℝ) 1,
      N₂ σ ≤ C * (F + b / (((1-σ)*r)/2)^2 * N₀ ((1+σ)/2) +
        2*a / (((1-σ)*r)/2) * N₁ ((1+σ)/2))) :
    phi (Ioo (1/2 : ℝ) 1) r 2 N₂ ≤
      ENNReal.ofReal (C*r^2/4*F +
        8*a*C*(phi (Ioo (1/2 : ℝ) 1) r 1 N₁).toReal +
        4*b*C*(phi (Ioo (1/2 : ℝ) 1) r 0 N₀).toReal) := by
  apply iSup_le
  intro σ
  apply iSup_le
  intro hσ
  have hm : (1+σ)/2 ∈ Ioo (1/2 : ℝ) 1 := by
    constructor <;> linarith [hσ.1,hσ.2]
  have hzero : N₀ ((1+σ)/2) ≤ (phi (Ioo (1/2 : ℝ) 1) r 0 N₀).toReal := by
    simpa only [pow_zero,one_mul] using
      phi_point_le_toReal (Ioo (1/2 : ℝ) 1) N₀ r 0 ((1+σ)/2) hm hP₀
  have hw : (1-(1+σ)/2)*r = ((1-σ)*r)/2 := by ring
  have hfirst : (((1-σ)*r)/2) * N₁ ((1+σ)/2) ≤
      (phi (Ioo (1/2 : ℝ) 1) r 1 N₁).toReal := by
    simpa only [pow_one,hw] using
      phi_point_le_toReal (Ioo (1/2 : ℝ) 1) N₁ r 1 ((1+σ)/2) hm hP₁
  apply ENNReal.ofReal_le_ofReal
  rw [← mul_pow]
  exact second_step_reweighted hr hσ hC ha hb hF (hstep σ hσ) hzero hfirst

end RothschildStein.H3

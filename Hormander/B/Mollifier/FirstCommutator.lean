-- Copyright (c) 2026 Scott Armstrong and Amélie Loher. All rights reserved.
-- Released under Apache 2.0 license as described in the file LICENSE.
module

public import Hormander.B.Mollifier.FirstKernel

@[expose] public section

noncomputable section

open MeasureTheory
open scoped FourierTransform ENNReal

namespace Hormander.B

variable {N : ℕ}

/-- The positive mollifier scales. -/
abbrev PosScale := {δ : ℝ // 0 < δ}

/-- The mollifier on Schwartz functions at a positive scale. -/
def mollOpS (N : ℕ) (d : PosScale) : Operator N := mollOp N d.1 d.2

theorem norm_derivSym_mul_diff_le (L : ℝ)
    (hL : ∀ (δ : ℝ) (hδ : 0 < δ) (i : Fin N) (ξ η : Carrier N),
      ‖coordC i ξ * mollSymbol N δ hδ ξ - coordC i η * mollSymbol N δ hδ η‖ ≤ L * ‖ξ - η‖)
    (δ : ℝ) (hδ : 0 < δ) (i : Fin N) (ξ η : Carrier N) :
    ‖derivSym i η * (mollSymbol N δ hδ ξ - mollSymbol N δ hδ η)‖ ≤
      2 * Real.pi * (1 + L) * ‖ξ - η‖ := by
  have hsplit : coordC i η * (mollSymbol N δ hδ ξ - mollSymbol N δ hδ η) =
      (coordC i η - coordC i ξ) * mollSymbol N δ hδ ξ +
        (coordC i ξ * mollSymbol N δ hδ ξ - coordC i η * mollSymbol N δ hδ η) := by ring
  have h1 : ‖coordC i η * (mollSymbol N δ hδ ξ - mollSymbol N δ hδ η)‖ ≤ (1 + L) * ‖ξ - η‖ := by
    rw [hsplit]
    refine (norm_add_le _ _).trans ?_
    have hc : ‖coordC i η - coordC i ξ‖ ≤ ‖ξ - η‖ := by
      rw [← coordC_sub, norm_sub_rev]; exact norm_coordC_le i _
    have := mul_le_mul hc (norm_mollSymbol_le δ hδ ξ) (norm_nonneg _) (norm_nonneg _)
    rw [norm_mul]
    nlinarith [hL δ hδ i ξ η]
  have : derivSym i η * (mollSymbol N δ hδ ξ - mollSymbol N δ hδ η) =
      (2 * Real.pi * Complex.I) * (coordC i η * (mollSymbol N δ hδ ξ - mollSymbol N δ hδ η)) := by
    unfold derivSym; ring
  rw [this, norm_mul]
  have hn : ‖(2 * (Real.pi : ℂ) * Complex.I)‖ = 2 * Real.pi := by
    simp [abs_of_pos Real.pi_pos]
  rw [hn]
  nlinarith [Real.pi_pos]

/-- The first mollifier commutator with `M_a ∂_i` is uniformly of order zero. -/
theorem uniformOrder_comm_moll_DOp (a : TestFunction N) (i : Fin N) :
    UniformOrder 0 (fun d : PosScale => operatorComm (mollOpS N d) (DOp a i)) := by
  obtain ⟨L, hL0, hL⟩ := mollSymbol_coord_lipschitz N
  apply uniformOrder_of_kernelBound
  intro s
  set κ : Carrier N → ℝ := fun α => (2 * Real.pi * (1 + L)) *
    (‖α‖ ^ 1 * (peetreOmega α ^ |s| * ‖𝓕 a α‖)) with hκdef
  have hint : Integrable κ := (integrable_kernelWeight (𝓕 a) 1 |s|).const_mul _
  have hκc : Continuous κ :=
    continuous_const.mul ((continuous_norm.pow 1).mul
      ((continuous_peetreOmega_rpow _).mul (𝓕 a).continuous.norm))
  have hκ0 : ∀ α, 0 ≤ κ α := fun α => by
    have := Real.rpow_nonneg (peetreOmega_pos α).le |s|
    simp only [hκdef]; positivity
  refine ⟨fun α => ENNReal.ofReal (κ α), ENNReal.measurable_ofReal.comp hκc.measurable,
    lintegral_ofReal_ne_top_of_integrable hint, fun d u ξ => ?_⟩
  refine fw_le_single s 0 _ u ξ _ (fourier_comm_moll_DOp d.1 d.2 a u i ξ) κ hκ0 fun α => ?_
  rw [add_zero, norm_mul, norm_mul, norm_mul]
  have hk := norm_derivSym_mul_diff_le L hL d.1 d.2 i ξ (ξ - α)
  rw [sub_sub_cancel, norm_mul] at hk
  have hp := peetre_jap ξ (ξ - α) s
  rw [sub_sub_cancel] at hp
  have h1 := Real.rpow_nonneg (japBracket_pos (ξ - α)).le s
  have hg := norm_nonneg (𝓕 a α)
  have hu := norm_nonneg (𝓕 u (ξ - α))
  have hJ := Real.rpow_nonneg (japBracket_pos ξ).le s
  have hpw := Real.rpow_nonneg (peetreOmega_pos α).le |s|
  calc japBracket ξ ^ s * (‖𝓕 a α‖ * (‖derivSym i (ξ - α)‖ * (‖mollSymbol N d.1 d.2 ξ -
          mollSymbol N d.1 d.2 (ξ - α)‖ * ‖𝓕 u (ξ - α)‖)))
      = japBracket ξ ^ s * (‖𝓕 a α‖ * ((‖derivSym i (ξ - α)‖ * ‖mollSymbol N d.1 d.2 ξ -
          mollSymbol N d.1 d.2 (ξ - α)‖) * ‖𝓕 u (ξ - α)‖)) := by ring
    _ ≤ (japBracket (ξ - α) ^ s * peetreOmega α ^ |s|) * (‖𝓕 a α‖ *
          ((2 * Real.pi * (1 + L) * ‖α‖) * ‖𝓕 u (ξ - α)‖)) := by
        refine mul_le_mul hp (mul_le_mul_of_nonneg_left
          (mul_le_mul_of_nonneg_right hk hu) hg) (by positivity) (by positivity)
    _ = _ := by simp only [hκdef]; ring

end Hormander.B

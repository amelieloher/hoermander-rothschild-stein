-- Copyright (c) 2026 Scott Armstrong and Amélie Loher. All rights reserved.
-- Released under Apache 2.0 license as described in the file LICENSE.
module

public import Hormander.B.Mollifier.SecondBound

@[expose] public section

noncomputable section

open MeasureTheory
open scoped FourierTransform ENNReal

namespace Hormander.B

variable {N : ℕ}

theorem peetreOmega_add_rpow_le (α β : Carrier N) (p : ℝ) (hp : 0 ≤ p) :
    peetreOmega (α + β) ^ p ≤ 2 ^ p * (peetreOmega α ^ p * peetreOmega β ^ p) := by
  calc peetreOmega (α + β) ^ p ≤ (2 * (peetreOmega α * peetreOmega β)) ^ p :=
        Real.rpow_le_rpow (peetreOmega_pos _).le (peetreOmega_add_le α β) hp
    _ = _ := by
        rw [Real.mul_rpow (by norm_num) (mul_nonneg (peetreOmega_pos α).le (peetreOmega_pos β).le),
          Real.mul_rpow (peetreOmega_pos α).le (peetreOmega_pos β).le]

/-- The double mollifier commutator with `M_a ∂_i` and `M_b ∂_k` is uniformly of order zero. -/
theorem uniformOrder_comm2_moll_DOp (a b : TestFunction N) (i k : Fin N) :
    UniformOrder 0 (fun d : PosScale =>
      operatorComm (operatorComm (mollOpS N d) (DOp a i)) (DOp b k)) := by
  obtain ⟨L, hL0, hL⟩ := mollSymbol_coord_lipschitz N
  obtain ⟨L₂, hL₂0, hL₂⟩ := mollSymbol_coord2_mixed N
  apply uniformOrder_of_kernelBound₂
  intro s
  set M := 2 + |s| with hM
  set Cc := (2 * Real.pi) ^ 2 * (L₂ + 4 * L + 2) * 2 ^ |s| with hCc
  set κ₁ : Carrier N → ℝ := fun α => Cc * (‖α‖ ^ 0 * (peetreOmega α ^ M * ‖𝓕 a α‖)) with hκ₁
  set κ₂ : Carrier N → ℝ := fun β => ‖β‖ ^ 0 * (peetreOmega β ^ M * ‖𝓕 b β‖) with hκ₂
  have hint₁ : Integrable κ₁ := (integrable_kernelWeight (𝓕 a) 0 M).const_mul _
  have hint₂ : Integrable κ₂ := integrable_kernelWeight (𝓕 b) 0 M
  have hκ₁c : Continuous κ₁ :=
    continuous_const.mul ((continuous_norm.pow 0).mul
      ((continuous_peetreOmega_rpow _).mul (𝓕 a).continuous.norm))
  have hκ₂c : Continuous κ₂ :=
    (continuous_norm.pow 0).mul ((continuous_peetreOmega_rpow _).mul (𝓕 b).continuous.norm)
  have hCc0 : 0 ≤ Cc := by simp only [hCc]; positivity
  have hκ₁0 : ∀ α, 0 ≤ κ₁ α := fun α => by
    have := Real.rpow_nonneg (peetreOmega_pos α).le M
    simp only [hκ₁]; positivity
  have hκ₂0 : ∀ β, 0 ≤ κ₂ β := fun β => by
    have := Real.rpow_nonneg (peetreOmega_pos β).le M
    simp only [hκ₂]; positivity
  refine ⟨fun a => ENNReal.ofReal (κ₁ a), fun b => ENNReal.ofReal (κ₂ b),
    ENNReal.measurable_ofReal.comp hκ₁c.measurable,
    ENNReal.measurable_ofReal.comp hκ₂c.measurable,
    lintegral_ofReal_ne_top_of_integrable hint₁, lintegral_ofReal_ne_top_of_integrable hint₂,
    fun d u ξ => ?_⟩
  refine fw_le_nested s 0 _ u ξ _ (fourier_comm2 d.1 d.2 a b u i k ξ) κ₁ κ₂ hκ₁0 hκ₂0
    fun α β => ?_
  simp only [tripleIntegrand]
  rw [add_zero, norm_mul, norm_mul, norm_mul]
  have hK := norm_cK_le L L₂ hL0 hL₂0 hL hL₂ d.1 d.2 i k ξ α β
  have hp := peetre_jap ξ (ξ - α - β) s
  have e : ξ - (ξ - α - β) = α + β := by abel
  rw [e] at hp
  have hpw : peetreOmega (α + β) ^ |s| ≤ 2 ^ |s| * (peetreOmega α ^ |s| * peetreOmega β ^ |s|) :=
    peetreOmega_add_rpow_le α β |s| (abs_nonneg s)
  have hJζ := Real.rpow_nonneg (japBracket_pos (ξ - α - β)).le s
  have hg := norm_nonneg (𝓕 a α)
  have hh := norm_nonneg (𝓕 b β)
  have hu := norm_nonneg (𝓕 u (ξ - α - β))
  have hA := Real.rpow_nonneg (peetreOmega_pos α).le |s|
  have hB := Real.rpow_nonneg (peetreOmega_pos β).le |s|
  have hJ1 : japBracket ξ ^ s ≤ japBracket (ξ - α - β) ^ s *
      (2 ^ |s| * (peetreOmega α ^ |s| * peetreOmega β ^ |s|)) :=
    hp.trans (mul_le_mul_of_nonneg_left hpw hJζ)
  have hωM : ∀ γ : Carrier N, peetreOmega γ ^ M = peetreOmega γ ^ (2 : ℝ) * peetreOmega γ ^ |s| :=
    fun γ => by rw [hM, Real.rpow_add (peetreOmega_pos γ)]
  have hω2 : ∀ γ : Carrier N, peetreOmega γ ^ (2 : ℝ) = peetreOmega γ ^ 2 := fun γ => Real.rpow_two _
  have hKb : ‖cK d.1 d.2 i k ξ α β‖ ≤ (2 * Real.pi) ^ 2 * (L₂ + 4 * L + 2) *
      (peetreOmega α ^ 2 * peetreOmega β ^ 2) := by
    refine hK.trans (le_of_eq ?_); ring
  have hm : 0 ≤ ‖cK d.1 d.2 i k ξ α β‖ := norm_nonneg _
  calc japBracket ξ ^ s * (‖𝓕 a α‖ * (‖𝓕 b β‖ * (‖cK d.1 d.2 i k ξ α β‖ * ‖𝓕 u (ξ - α - β)‖)))
      = japBracket ξ ^ s * (‖𝓕 a α‖ * (‖𝓕 b β‖ * (‖cK d.1 d.2 i k ξ α β‖ * ‖𝓕 u (ξ - α - β)‖))) := rfl
    _ ≤ (japBracket (ξ - α - β) ^ s *
          (2 ^ |s| * (peetreOmega α ^ |s| * peetreOmega β ^ |s|))) *
        (‖𝓕 a α‖ * (‖𝓕 b β‖ * (((2 * Real.pi) ^ 2 * (L₂ + 4 * L + 2) *
          (peetreOmega α ^ 2 * peetreOmega β ^ 2)) * ‖𝓕 u (ξ - α - β)‖))) := by
        refine mul_le_mul hJ1 (mul_le_mul_of_nonneg_left (mul_le_mul_of_nonneg_left
          (mul_le_mul_of_nonneg_right hKb hu) hh) hg) (by positivity) (by positivity)
    _ = _ := by
        simp only [hκ₁, hκ₂, hCc, hωM, hω2, pow_zero, one_mul]
        ring

end Hormander.B

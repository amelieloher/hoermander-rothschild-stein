-- Copyright (c) 2026 Scott Armstrong and Amélie Loher. All rights reserved.
-- Released under Apache 2.0 license as described in the file LICENSE.
module

public import Hormander.B.Mollifier.FirstCommutator

@[expose] public section

noncomputable section

open MeasureTheory
open scoped FourierTransform ENNReal

namespace Hormander.B

variable {N : ℕ}

theorem norm_sub_le_omega (ξ α : Carrier N) : ‖ξ - α‖ ≤ (1 + ‖ξ‖) * peetreOmega α := by
  have h1 : ‖α‖ ≤ peetreOmega α := by
    refine (norm_le_japBracket α).trans ?_
    unfold peetreOmega
    nlinarith [japBracket_pos α, (by rw [Real.one_le_sqrt]; norm_num : (1:ℝ) ≤ Real.sqrt 2)]
  have h2 := one_le_peetreOmega α
  calc ‖ξ - α‖ ≤ ‖ξ‖ + ‖α‖ := norm_sub_le _ _
    _ ≤ _ := by nlinarith [norm_nonneg ξ]

theorem norm_sub_sub_le_omega (ξ α β : Carrier N) :
    ‖ξ - α - β‖ ≤ 2 * (1 + ‖ξ‖) * (peetreOmega α * peetreOmega β) := by
  have h1 : ‖α‖ ≤ peetreOmega α := by
    refine (norm_le_japBracket α).trans ?_
    unfold peetreOmega
    nlinarith [japBracket_pos α, (by rw [Real.one_le_sqrt]; norm_num : (1:ℝ) ≤ Real.sqrt 2)]
  have h1' : ‖β‖ ≤ peetreOmega β := by
    refine (norm_le_japBracket β).trans ?_
    unfold peetreOmega
    nlinarith [japBracket_pos β, (by rw [Real.one_le_sqrt]; norm_num : (1:ℝ) ≤ Real.sqrt 2)]
  have h3 := one_le_peetreOmega β
  have h4 := one_le_peetreOmega α
  have hξ := norm_nonneg ξ
  calc ‖ξ - α - β‖ ≤ ‖ξ‖ + ‖α‖ + ‖β‖ := by
        calc ‖ξ - α - β‖ ≤ ‖ξ - α‖ + ‖β‖ := norm_sub_le _ _
          _ ≤ ‖ξ‖ + ‖α‖ + ‖β‖ := by linarith [norm_sub_le ξ α]
    _ ≤ _ := by
        nlinarith [mul_nonneg (sub_nonneg.2 h3) (sub_nonneg.2 h4),
          mul_nonneg hξ (mul_nonneg (sub_nonneg.2 h3) (sub_nonneg.2 h4)),
          mul_nonneg hξ (sub_nonneg.2 h3), mul_nonneg hξ (sub_nonneg.2 h4)]

/-- Coefficient of the term `S D_a D_b`. -/
def cT1 (δ : ℝ) (hδ : 0 < δ) (i k : Fin N) (ξ α β : Carrier N) : ℂ :=
  mollSymbol N δ hδ ξ * (derivSym i (ξ - α) * derivSym k (ξ - α - β))

/-- Coefficient of the term `D_a S D_b`. -/
def cT2 (δ : ℝ) (hδ : 0 < δ) (i k : Fin N) (ξ α β : Carrier N) : ℂ :=
  mollSymbol N δ hδ (ξ - α) * (derivSym i (ξ - α) * derivSym k (ξ - α - β))

/-- Coefficient of the term `D_b S D_a`. -/
def cT3 (δ : ℝ) (hδ : 0 < δ) (i k : Fin N) (ξ α β : Carrier N) : ℂ :=
  mollSymbol N δ hδ (ξ - β) * (derivSym k (ξ - β) * derivSym i (ξ - α - β))

/-- Coefficient of the term `D_b D_a S`. -/
def cT4 (δ : ℝ) (hδ : 0 < δ) (i k : Fin N) (ξ α β : Carrier N) : ℂ :=
  mollSymbol N δ hδ (ξ - α - β) * (derivSym k (ξ - β) * derivSym i (ξ - α - β))

theorem continuous_cT (δ : ℝ) (hδ : 0 < δ) (i k : Fin N) (ξ : Carrier N) :
    Continuous (fun p : Carrier N × Carrier N => cT1 δ hδ i k ξ p.1 p.2) ∧
    Continuous (fun p : Carrier N × Carrier N => cT2 δ hδ i k ξ p.1 p.2) ∧
    Continuous (fun p : Carrier N × Carrier N => cT3 δ hδ i k ξ p.1 p.2) ∧
    Continuous (fun p : Carrier N × Carrier N => cT4 δ hδ i k ξ p.1 p.2) := by
  have hm := continuous_mollSymbol (N := N) δ hδ
  have hi := continuous_derivSym (N := N) i
  have hk := continuous_derivSym (N := N) k
  have c1 : Continuous fun p : Carrier N × Carrier N => ξ - p.1 := continuous_const.sub continuous_fst
  have c2 : Continuous fun p : Carrier N × Carrier N => ξ - p.2 := continuous_const.sub continuous_snd
  have c3 : Continuous fun p : Carrier N × Carrier N => ξ - p.1 - p.2 := c1.sub continuous_snd
  refine ⟨?_, ?_, ?_, ?_⟩
  · exact continuous_const.mul ((hi.comp c1).mul (hk.comp c3))
  · exact (hm.comp c1).mul ((hi.comp c1).mul (hk.comp c3))
  · exact (hm.comp c2).mul ((hk.comp c2).mul (hi.comp c3))
  · exact (hm.comp c3).mul ((hk.comp c2).mul (hi.comp c3))

theorem norm_cT_le (δ : ℝ) (hδ : 0 < δ) (i k : Fin N) (ξ α β : Carrier N) :
    ‖cT1 δ hδ i k ξ α β‖ ≤ (4 * Real.pi * (1 + ‖ξ‖)) ^ 2 * (peetreOmega α ^ 2 * peetreOmega β ^ 2) ∧
    ‖cT2 δ hδ i k ξ α β‖ ≤ (4 * Real.pi * (1 + ‖ξ‖)) ^ 2 * (peetreOmega α ^ 2 * peetreOmega β ^ 2) ∧
    ‖cT3 δ hδ i k ξ α β‖ ≤ (4 * Real.pi * (1 + ‖ξ‖)) ^ 2 * (peetreOmega α ^ 2 * peetreOmega β ^ 2) ∧
    ‖cT4 δ hδ i k ξ α β‖ ≤ (4 * Real.pi * (1 + ‖ξ‖)) ^ 2 * (peetreOmega α ^ 2 * peetreOmega β ^ 2) := by
  set W := 4 * Real.pi * (1 + ‖ξ‖) with hW
  have hW0 : 0 ≤ W := by positivity
  have oa := one_le_peetreOmega α
  have ob := one_le_peetreOmega β
  have dα : ‖derivSym i (ξ - α)‖ ≤ W * peetreOmega α := by
    refine (norm_derivSym i _).trans ?_
    have := norm_sub_le_omega ξ α
    calc 2 * Real.pi * ‖ξ - α‖ ≤ 2 * Real.pi * ((1 + ‖ξ‖) * peetreOmega α) :=
          mul_le_mul_of_nonneg_left this (by positivity)
      _ ≤ _ := by rw [hW]; nlinarith [Real.pi_pos, mul_nonneg (mul_nonneg Real.pi_pos.le (by positivity : (0:ℝ) ≤ 1 + ‖ξ‖)) (by linarith : (0:ℝ) ≤ peetreOmega α)]
  have dβ : ‖derivSym k (ξ - β)‖ ≤ W * peetreOmega β := by
    refine (norm_derivSym k _).trans ?_
    have := norm_sub_le_omega ξ β
    calc 2 * Real.pi * ‖ξ - β‖ ≤ 2 * Real.pi * ((1 + ‖ξ‖) * peetreOmega β) :=
          mul_le_mul_of_nonneg_left this (by positivity)
      _ ≤ _ := by rw [hW]; nlinarith [Real.pi_pos, mul_nonneg (mul_nonneg Real.pi_pos.le (by positivity : (0:ℝ) ≤ 1 + ‖ξ‖)) (by linarith : (0:ℝ) ≤ peetreOmega β)]
  have dαβk : ‖derivSym k (ξ - α - β)‖ ≤ W * (peetreOmega α * peetreOmega β) := by
    refine (norm_derivSym k _).trans ?_
    have := norm_sub_sub_le_omega ξ α β
    calc 2 * Real.pi * ‖ξ - α - β‖ ≤ 2 * Real.pi * (2 * (1 + ‖ξ‖) * (peetreOmega α * peetreOmega β)) :=
          mul_le_mul_of_nonneg_left this (by positivity)
      _ = _ := by rw [hW]; ring
  have dαβi : ‖derivSym i (ξ - α - β)‖ ≤ W * (peetreOmega α * peetreOmega β) := by
    refine (norm_derivSym i _).trans ?_
    have := norm_sub_sub_le_omega ξ α β
    calc 2 * Real.pi * ‖ξ - α - β‖ ≤ 2 * Real.pi * (2 * (1 + ‖ξ‖) * (peetreOmega α * peetreOmega β)) :=
          mul_le_mul_of_nonneg_left this (by positivity)
      _ = _ := by rw [hW]; ring
  have target : ∀ x : ℝ, x ≤ W ^ 2 * (peetreOmega α * peetreOmega α * peetreOmega β) →
      x ≤ W ^ 2 * (peetreOmega α ^ 2 * peetreOmega β ^ 2) := fun x hx =>
    hx.trans (by
      have : peetreOmega α * peetreOmega α * peetreOmega β ≤ peetreOmega α ^ 2 * peetreOmega β ^ 2 := by
        nlinarith [mul_nonneg (mul_nonneg (by linarith : (0:ℝ) ≤ peetreOmega α) (by linarith : (0:ℝ) ≤ peetreOmega α)) (sub_nonneg.2 ob), mul_nonneg (mul_nonneg (by linarith : (0:ℝ) ≤ peetreOmega α) (by linarith : (0:ℝ) ≤ peetreOmega α)) (mul_nonneg (by linarith : (0:ℝ) ≤ peetreOmega β) (sub_nonneg.2 ob))]
      exact mul_le_mul_of_nonneg_left this (by positivity))
  have target2 : ∀ x : ℝ, x ≤ W ^ 2 * (peetreOmega α * (peetreOmega β * peetreOmega β)) →
      x ≤ W ^ 2 * (peetreOmega α ^ 2 * peetreOmega β ^ 2) := fun x hx =>
    hx.trans (by
      have : peetreOmega α * (peetreOmega β * peetreOmega β) ≤ peetreOmega α ^ 2 * peetreOmega β ^ 2 := by
        nlinarith [mul_nonneg (mul_nonneg (by linarith : (0:ℝ) ≤ peetreOmega β) (by linarith : (0:ℝ) ≤ peetreOmega β)) (sub_nonneg.2 oa), mul_nonneg (mul_nonneg (by linarith : (0:ℝ) ≤ peetreOmega β) (by linarith : (0:ℝ) ≤ peetreOmega β)) (mul_nonneg (by linarith : (0:ℝ) ≤ peetreOmega α) (sub_nonneg.2 oa))]
      exact mul_le_mul_of_nonneg_left this (by positivity))
  have hm := norm_mollSymbol_le (N := N) δ hδ
  have mul2 : ∀ (x y : ℂ) (px py : ℝ), ‖x‖ ≤ px → ‖y‖ ≤ py → 0 ≤ px → ‖x * y‖ ≤ px * py := fun x y px py hx hy hp0 => by
    rw [norm_mul]; exact mul_le_mul hx hy (norm_nonneg _) hp0
  refine ⟨?_, ?_, ?_, ?_⟩
  · unfold cT1
    have := mul2 _ _ _ _ dα dαβk (by positivity)
    have h2 := mul2 (mollSymbol N δ hδ ξ) _ 1 _ (hm ξ) this zero_le_one
    refine target _ ?_
    nlinarith [h2, mul_nonneg hW0 hW0]
  · unfold cT2
    have := mul2 _ _ _ _ dα dαβk (by positivity)
    have h2 := mul2 (mollSymbol N δ hδ (ξ - α)) _ 1 _ (hm _) this zero_le_one
    refine target _ ?_
    nlinarith [h2, mul_nonneg hW0 hW0]
  · unfold cT3
    have := mul2 _ _ _ _ dβ dαβi (by positivity)
    have h2 := mul2 (mollSymbol N δ hδ (ξ - β)) _ 1 _ (hm _) this zero_le_one
    refine target2 _ ?_
    nlinarith [h2, mul_nonneg hW0 hW0]
  · unfold cT4
    have := mul2 _ _ _ _ dβ dαβi (by positivity)
    have h2 := mul2 (mollSymbol N δ hδ (ξ - α - β)) _ 1 _ (hm _) this zero_le_one
    refine target2 _ ?_
    nlinarith [h2, mul_nonneg hW0 hW0]

end Hormander.B

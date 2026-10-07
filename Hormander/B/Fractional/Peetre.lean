-- Copyright (c) 2026 Scott Armstrong and Amélie Loher. All rights reserved.
-- Released under Apache 2.0 license as described in the file LICENSE.
module

public import Hormander.B.Fractional.Taylor
public import Hormander.A.SobolevScale
public import Hormander.B.Fractional.SobolevFourier

@[expose] public section

noncomputable section

open MeasureTheory
open scoped FourierTransform

namespace Hormander.B

/-- The Peetre-normalized bracket `√2 ⟨x⟩`. -/
def peetreOmega {E : Type*} [NormedAddCommGroup E] (x : E) : ℝ := Real.sqrt 2 * japBracket x

section

variable {E : Type*} [NormedAddCommGroup E]

theorem one_le_peetreOmega (x : E) : 1 ≤ peetreOmega x := by
  unfold peetreOmega
  have h2 : (1 : ℝ) ≤ Real.sqrt 2 := by
    rw [Real.one_le_sqrt]; norm_num
  nlinarith [one_le_japBracket x]

theorem peetreOmega_pos (x : E) : 0 < peetreOmega x :=
  lt_of_lt_of_le one_pos (one_le_peetreOmega x)

theorem peetreOmega_mono {x y : E} (h : ‖x‖ ≤ ‖y‖) : peetreOmega x ≤ peetreOmega y := by
  unfold peetreOmega
  apply mul_le_mul_of_nonneg_left _ (Real.sqrt_nonneg _)
  unfold japBracket bracketSq
  apply Real.sqrt_le_sqrt
  nlinarith [norm_nonneg x]

theorem peetreOmega_add_le (x y : E) : peetreOmega (x + y) ≤ 2 * (peetreOmega x * peetreOmega y) := by
  have h1 := japBracketLipschitz (x + y) x
  rw [add_sub_cancel_left] at h1
  have h1' : japBracket (x + y) ≤ japBracket x + ‖y‖ := by
    have := (abs_le.1 h1).2
    linarith
  have hy := norm_le_japBracket y
  have hx1 := one_le_japBracket x
  have hy1 := one_le_japBracket y
  have : japBracket (x + y) ≤ 2 * (japBracket x * japBracket y) := by nlinarith
  unfold peetreOmega
  have h2 : Real.sqrt 2 * Real.sqrt 2 = 2 := Real.mul_self_sqrt (by norm_num)
  have h2' : Real.sqrt 2 ≤ 2 := by
    rw [Real.sqrt_le_left (by norm_num)]; norm_num
  have h3 := mul_le_mul_of_nonneg_left this (Real.sqrt_nonneg 2)
  have hp := mul_pos (japBracket_pos x) (japBracket_pos y)
  calc Real.sqrt 2 * japBracket (x + y) ≤ Real.sqrt 2 * (2 * (japBracket x * japBracket y)) := h3
    _ ≤ 2 * (2 * (japBracket x * japBracket y)) :=
        mul_le_mul_of_nonneg_right h2' (by positivity)
    _ = 2 * (Real.sqrt 2 * japBracket x * (Real.sqrt 2 * japBracket y)) := by
        rw [show Real.sqrt 2 * japBracket x * (Real.sqrt 2 * japBracket y) =
          (Real.sqrt 2 * Real.sqrt 2) * (japBracket x * japBracket y) by ring, h2]

theorem peetreOmega_add_smul_le [NormedSpace ℝ E] (x y : E) (t : ℝ) (ht0 : 0 ≤ t) (ht1 : t ≤ 1) :
    peetreOmega (x + t • y) ≤ 2 * (peetreOmega x * peetreOmega y) := by
  refine (peetreOmega_add_le x (t • y)).trans ?_
  have hty : peetreOmega (t • y) ≤ peetreOmega y := by
    apply peetreOmega_mono
    rw [norm_smul, Real.norm_eq_abs, abs_of_nonneg ht0]
    exact mul_le_of_le_one_left (norm_nonneg y) ht1
  have hxp := peetreOmega_pos x
  have := mul_le_mul_of_nonneg_left hty hxp.le
  linarith

end

variable {N : ℕ}

/-- Peetre's inequality for real powers of the Japanese bracket. -/
theorem peetre_jap (x y : Carrier N) (p : ℝ) :
    japBracket x ^ p ≤ japBracket y ^ p * peetreOmega (x - y) ^ |p| := by
  have h := peetreWeight x y p
  have hy := japBracket_pos y
  have hyp : 0 < japBracket y ^ p := Real.rpow_pos_of_pos hy p
  rw [Real.div_rpow (bracketSq_pos' x).le (bracketSq_pos' y).le, ← japBracket_rpow,
    ← japBracket_rpow, div_le_iff₀ hyp] at h
  have e : (2 * bracketSq (x - y)) ^ (|p| / 2) = peetreOmega (x - y) ^ |p| := by
    unfold peetreOmega
    rw [Real.mul_rpow (by norm_num) (bracketSq_pos' _).le,
      Real.mul_rpow (Real.sqrt_nonneg 2) (japBracket_pos _).le, japBracket_rpow,
      Real.sqrt_eq_rpow, ← Real.rpow_mul (by norm_num)]
    congr 2
    ring
  rw [e] at h
  linarith


/-- Product of two bracket powers, moving the first to the second base point. -/
theorem jap_pow_mul_le (x y : Carrier N) (p q : ℝ) :
    japBracket x ^ p * japBracket y ^ q ≤
      japBracket y ^ (p + q) * peetreOmega (x - y) ^ |p| := by
  rw [Real.rpow_add (japBracket_pos y)]
  have h := peetre_jap x y p
  have hq : 0 < japBracket y ^ q := Real.rpow_pos_of_pos (japBracket_pos y) q
  calc japBracket x ^ p * japBracket y ^ q ≤
        (japBracket y ^ p * peetreOmega (x - y) ^ |p|) * japBracket y ^ q :=
        mul_le_mul_of_nonneg_right h hq.le
    _ = _ := by ring

theorem integrable_japBracket_mul {N : ℕ} (φ : TestFunction N) (M : ℝ) :
    Integrable (fun a : Carrier N => japBracket a ^ M * ‖φ a‖) := by
  set ψ : TestFunction N := SchwartzMap.smulLeftCLM ℂ (Hormander.A.besselSymbol M) φ with hψdef
  have hψ0 : Integrable (ψ : Carrier N → ℂ) := ψ.integrable
  have hψ := hψ0.norm
  refine hψ.congr (Filter.Eventually.of_forall fun a => ?_)
  simp only
  rw [SchwartzMap.smulLeftCLM_apply_apply (Hormander.A.besselSymbol_hasTemperateGrowth M),
    norm_smul, norm_besselSymbol]

theorem integrable_peetreOmega_mul {N : ℕ} (φ : TestFunction N) (M : ℝ) :
    Integrable (fun a : Carrier N => peetreOmega a ^ M * ‖φ a‖) := by
  have := (integrable_japBracket_mul φ M).const_mul (Real.sqrt 2 ^ M)
  refine this.congr (Filter.Eventually.of_forall fun a => ?_)
  simp only [peetreOmega]
  rw [Real.mul_rpow (Real.sqrt_nonneg 2) (japBracket_pos a).le]
  ring

/-- Polynomially weighted Schwartz functions are integrable. -/
theorem integrable_kernelWeight {N : ℕ} (φ : TestFunction N) (j : ℕ) (M : ℝ) :
    Integrable (fun a : Carrier N => ‖a‖ ^ j * (peetreOmega a ^ M * ‖φ a‖)) := by
  refine ((integrable_peetreOmega_mul φ (M + j))).mono' ?_ ?_
  · have h1 : Continuous fun a : Carrier N => peetreOmega a ^ M := by
      have hc : Continuous fun a : Carrier N => peetreOmega a := by
        unfold peetreOmega japBracket bracketSq
        fun_prop
      exact hc.rpow_const fun a => Or.inl (peetreOmega_pos a).ne'
    exact ((continuous_norm.pow j).mul (h1.mul φ.continuous.norm)).aestronglyMeasurable
  · refine Filter.Eventually.of_forall fun a => ?_
    have hn : ‖a‖ ^ j ≤ peetreOmega a ^ (j : ℝ) := by
      rw [Real.rpow_natCast]
      exact pow_le_pow_left₀ (norm_nonneg a)
        ((norm_le_japBracket a).trans (by unfold peetreOmega; nlinarith [one_le_japBracket a,
          (by rw [Real.one_le_sqrt]; norm_num : (1:ℝ) ≤ Real.sqrt 2)])) j
    rw [Real.norm_eq_abs, abs_of_nonneg (mul_nonneg (pow_nonneg (norm_nonneg a) j)
      (mul_nonneg (Real.rpow_nonneg (peetreOmega_pos a).le M) (norm_nonneg (φ a)))),
      Real.rpow_add (peetreOmega_pos a)]
    have := mul_le_mul_of_nonneg_right hn (mul_nonneg (Real.rpow_nonneg (peetreOmega_pos a).le M)
      (norm_nonneg (φ a)))
    nlinarith [this]

end Hormander.B

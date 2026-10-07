-- Copyright (c) 2026 Scott Armstrong and Amélie Loher. All rights reserved.
-- Released under Apache 2.0 license as described in the file LICENSE.
module

public import Hormander.B.Fractional.Peetre
public import Hormander.B.WeightEstimates

@[expose] public section

noncomputable section

open scoped RealInnerProductSpace

namespace Hormander.B

variable {N : ℕ}

theorem rpow_add_three (x : ℝ) (hx : 0 < x) (p q : ℝ) : x ^ p * x ^ q = x ^ (p + q) :=
  (Real.rpow_add hx p q).symm

/-- Single-commutator kernel bound, after Peetre. -/
theorem kernel_single_bound (σ s : ℝ) (ξ a : Carrier N) :
    japBracket ξ ^ s * |japBracket ξ ^ σ - japBracket (ξ - a) ^ σ| ≤
      |σ| * ‖a‖ * (peetreOmega a ^ |s + σ - 1| + peetreOmega a ^ |s|) *
        japBracket (ξ - a) ^ (s + σ - 1) := by
  have hJ := Real.rpow_nonneg (japBracket_pos ξ).le s
  have h8 := besselWeightDifference ξ (ξ - a) σ
  rw [sub_sub_cancel] at h8
  have t1 : japBracket ξ ^ s * japBracket ξ ^ (σ - 1) ≤
      japBracket (ξ - a) ^ (s + σ - 1) * peetreOmega a ^ |s + σ - 1| := by
    rw [rpow_add_three _ (japBracket_pos ξ), show s + (σ - 1) = s + σ - 1 by ring]
    have := peetre_jap ξ (ξ - a) (s + σ - 1)
    rwa [sub_sub_cancel] at this
  have t2 : japBracket ξ ^ s * japBracket (ξ - a) ^ (σ - 1) ≤
      japBracket (ξ - a) ^ (s + σ - 1) * peetreOmega a ^ |s| := by
    have := jap_pow_mul_le ξ (ξ - a) s (σ - 1)
    rwa [sub_sub_cancel, show s + (σ - 1) = s + σ - 1 by ring] at this
  calc japBracket ξ ^ s * |japBracket ξ ^ σ - japBracket (ξ - a) ^ σ|
      ≤ japBracket ξ ^ s * (|σ| * ‖a‖ *
          (japBracket ξ ^ (σ - 1) + japBracket (ξ - a) ^ (σ - 1))) :=
        mul_le_mul_of_nonneg_left h8 hJ
    _ = |σ| * ‖a‖ * (japBracket ξ ^ s * japBracket ξ ^ (σ - 1) +
          japBracket ξ ^ s * japBracket (ξ - a) ^ (σ - 1)) := by ring
    _ ≤ |σ| * ‖a‖ * (japBracket (ξ - a) ^ (s + σ - 1) * peetreOmega a ^ |s + σ - 1| +
          japBracket (ξ - a) ^ (s + σ - 1) * peetreOmega a ^ |s|) := by
        gcongr
    _ = _ := by ring

/-- The mixed second difference of a bracket power is bounded by
the product of the increments times the endpoint weights along an interior segment point. -/
theorem mixed_difference_bound (σ : ℝ) (ζ a b : Carrier N) :
    ∃ θ : ℝ, 0 < θ ∧ θ < 1 ∧
      |japBracket (ζ + a + b) ^ σ - japBracket (ζ + a) ^ σ - japBracket (ζ + b) ^ σ +
          japBracket ζ ^ σ| ≤
        gradConst σ * ‖a‖ * ‖b‖ *
          (japBracket (ζ + θ • b) ^ (σ - 2) + japBracket (ζ + θ • b + a) ^ (σ - 2)) := by
  set f : ℝ → ℝ := fun s => bracketSq (ζ + a + s • b) ^ (σ / 2) -
    bracketSq (ζ + s • b) ^ (σ / 2) with hf
  have hd : ∀ s : ℝ, HasDerivAt f (gradPair σ b (ζ + a + s • b) - gradPair σ b (ζ + s • b)) s :=
    fun s => (hasDerivAt_weight_segment σ (ζ + a) b s).sub (hasDerivAt_weight_segment σ ζ b s)
  obtain ⟨c, hc, hceq⟩ := exists_hasDerivAt_eq_slope f _ (zero_lt_one)
    (fun s _ => (hd s).continuousAt.continuousWithinAt) (fun s _ => hd s)
  refine ⟨c, hc.1, hc.2, ?_⟩
  have h1 : f 1 - f 0 = japBracket (ζ + a + b) ^ σ - japBracket (ζ + a) ^ σ -
      japBracket (ζ + b) ^ σ + japBracket ζ ^ σ := by
    simp only [hf, one_smul, zero_smul, add_zero, japBracket_rpow]
    ring
  simp only [sub_zero, div_one] at hceq
  rw [← h1, ← hceq]
  have := gradPair_difference_bound σ (ζ + c • b) a b
  rw [add_right_comm ζ a (c • b)]
  exact this

theorem kernel_triple_core (σ s : ℝ) (ζ a b : Carrier N) :
    japBracket (ζ + a + b) ^ s *
        |japBracket (ζ + a + b) ^ σ - japBracket (ζ + a) ^ σ - japBracket (ζ + b) ^ σ +
          japBracket ζ ^ σ| ≤
      2 * gradConst σ * 2 ^ (|s| + |σ - 2|) *
        ((‖a‖ * peetreOmega a ^ (|s| + |σ - 2|)) * (‖b‖ * peetreOmega b ^ (|s| + |σ - 2|))) *
        japBracket ζ ^ (s + σ - 2) := by
  obtain ⟨θ, hθ0, hθ1, hmix⟩ := mixed_difference_bound σ ζ a b
  set M := |s| + |σ - 2| with hM
  have hJζ := japBracket_pos ζ
  have hωa := peetreOmega_pos a
  have hωb := peetreOmega_pos b
  set W := 2 * (peetreOmega a * peetreOmega b) with hW
  have hW0 : 0 < W := by positivity
  have hWb : peetreOmega b ≤ W := by
    have := one_le_peetreOmega a
    nlinarith
  have hp0 : 0 ≤ |σ - 2| := abs_nonneg _
  have hs0 : 0 ≤ |s| := abs_nonneg _
  -- weight comparisons
  have P1 : japBracket (ζ + θ • b) ^ (σ - 2) ≤ japBracket ζ ^ (σ - 2) * W ^ |σ - 2| := by
    have h := peetre_jap (ζ + θ • b) ζ (σ - 2)
    rw [add_sub_cancel_left] at h
    refine h.trans (mul_le_mul_of_nonneg_left ?_ (Real.rpow_nonneg hJζ.le _))
    refine Real.rpow_le_rpow (peetreOmega_pos _).le ?_ hp0
    refine (peetreOmega_mono ?_).trans hWb
    rw [norm_smul, Real.norm_eq_abs, abs_of_nonneg hθ0.le]
    exact mul_le_of_le_one_left (norm_nonneg b) hθ1.le
  have P2 : japBracket (ζ + θ • b + a) ^ (σ - 2) ≤ japBracket ζ ^ (σ - 2) * W ^ |σ - 2| := by
    have h := peetre_jap (ζ + θ • b + a) ζ (σ - 2)
    rw [show ζ + θ • b + a - ζ = a + θ • b by abel] at h
    refine h.trans (mul_le_mul_of_nonneg_left ?_ (Real.rpow_nonneg hJζ.le _))
    exact Real.rpow_le_rpow (peetreOmega_pos _).le (peetreOmega_add_smul_le a b θ hθ0.le hθ1.le) hp0
  have P3 : japBracket (ζ + a + b) ^ s ≤ japBracket ζ ^ s * W ^ |s| := by
    have h := peetre_jap (ζ + a + b) ζ s
    rw [show ζ + a + b - ζ = a + b by abel] at h
    refine h.trans (mul_le_mul_of_nonneg_left ?_ (Real.rpow_nonneg hJζ.le _))
    exact Real.rpow_le_rpow (peetreOmega_pos _).le (peetreOmega_add_le a b) hs0
  have hmix' : |japBracket (ζ + a + b) ^ σ - japBracket (ζ + a) ^ σ - japBracket (ζ + b) ^ σ +
          japBracket ζ ^ σ| ≤ gradConst σ * ‖a‖ * ‖b‖ *
          (2 * (japBracket ζ ^ (σ - 2) * W ^ |σ - 2|)) := by
    refine hmix.trans (mul_le_mul_of_nonneg_left ?_ (by
      have := gradConst_nonneg σ; positivity))
    linarith
  have hWpow : W ^ |s| * W ^ |σ - 2| = 2 ^ M * (peetreOmega a ^ M * peetreOmega b ^ M) := by
    rw [← Real.rpow_add hW0, ← hM, hW, Real.mul_rpow (by norm_num)
      (mul_nonneg hωa.le hωb.le), Real.mul_rpow hωa.le hωb.le]
  have hgc := gradConst_nonneg σ
  have hJs := Real.rpow_nonneg hJζ.le s
  have hJσ := Real.rpow_nonneg hJζ.le (σ - 2)
  have hWs := Real.rpow_nonneg hW0.le |s|
  have hWp := Real.rpow_nonneg hW0.le |σ - 2|
  calc japBracket (ζ + a + b) ^ s * |japBracket (ζ + a + b) ^ σ - japBracket (ζ + a) ^ σ -
          japBracket (ζ + b) ^ σ + japBracket ζ ^ σ|
      ≤ (japBracket ζ ^ s * W ^ |s|) * (gradConst σ * ‖a‖ * ‖b‖ *
          (2 * (japBracket ζ ^ (σ - 2) * W ^ |σ - 2|))) :=
        mul_le_mul P3 hmix' (abs_nonneg _) (by positivity)
    _ = 2 * gradConst σ * (‖a‖ * ‖b‖) * (japBracket ζ ^ s * japBracket ζ ^ (σ - 2)) *
          (W ^ |s| * W ^ |σ - 2|) := by ring
    _ = _ := by
        rw [rpow_add_three _ hJζ, hWpow, show s + (σ - 2) = s + σ - 2 by ring]
        ring

/-- Nested-commutator kernel bound, after Peetre. -/
theorem kernel_triple_bound (σ s : ℝ) (ξ a b : Carrier N) :
    japBracket ξ ^ s *
        |japBracket ξ ^ σ - japBracket (ξ - a) ^ σ - japBracket (ξ - b) ^ σ +
          japBracket (ξ - a - b) ^ σ| ≤
      2 * gradConst σ * 2 ^ (|s| + |σ - 2|) *
        ((‖a‖ * peetreOmega a ^ (|s| + |σ - 2|)) * (‖b‖ * peetreOmega b ^ (|s| + |σ - 2|))) *
        japBracket (ξ - a - b) ^ (s + σ - 2) := by
  have h := kernel_triple_core σ s (ξ - a - b) a b
  have e1 : ξ - a - b + a + b = ξ := by abel
  have e2 : ξ - a - b + a = ξ - b := by abel
  have e3 : ξ - a - b + b = ξ - a := by abel
  rw [e1, e2, e3] at h
  have : japBracket ξ ^ σ - japBracket (ξ - a) ^ σ - japBracket (ξ - b) ^ σ +
      japBracket (ξ - a - b) ^ σ = japBracket ξ ^ σ - japBracket (ξ - b) ^ σ -
      japBracket (ξ - a) ^ σ + japBracket (ξ - a - b) ^ σ := by ring
  rw [this]
  exact h

end Hormander.B

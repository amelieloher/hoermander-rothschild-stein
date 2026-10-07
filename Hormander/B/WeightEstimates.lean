-- Copyright (c) 2026 Scott Armstrong and Amélie Loher. All rights reserved.
-- Released under Apache 2.0 license as described in the file LICENSE.
module

public import Hormander.B.Defs
public import Mathlib.Analysis.Calculus.Deriv.MeanValue
public import Mathlib.Analysis.SpecialFunctions.Pow.Deriv

@[expose] public section

noncomputable section

namespace Hormander.B

/-- The square of the Japanese bracket, written without a square root. -/
def bracketSq {E : Type*} [NormedAddCommGroup E] (x : E) : ℝ := 1 + ‖x‖ ^ 2

/-- The Japanese bracket on the Euclidean carrier. -/
def japBracket {E : Type*} [NormedAddCommGroup E] (x : E) : ℝ := Real.sqrt (bracketSq x)

/-- Peetre's inequality for the squared Japanese bracket weights. -/
theorem peetreWeight {N : ℕ} (x y : Carrier N) (s : ℝ) :
    ((bracketSq x / bracketSq y) ^ (s / 2)) ≤
      (2 * bracketSq (x - y)) ^ (|s| / 2) := by
  have hbracket_pos (z : Carrier N) : 0 < bracketSq z := by
    unfold bracketSq
    positivity
  have hbase (u v : Carrier N) :
      bracketSq u ≤ 2 * bracketSq (u - v) * bracketSq v := by
    have hnorm : ‖u‖ ≤ ‖u - v‖ + ‖v‖ := by
      calc
        ‖u‖ = ‖(u - v) + v‖ := by congr 1; abel
        _ ≤ ‖u - v‖ + ‖v‖ := norm_add_le _ _
    have hnorm_sq : ‖u‖ ^ 2 ≤ (‖u - v‖ + ‖v‖) ^ 2 := by
      have hsum_nonneg : 0 ≤ ‖u - v‖ + ‖v‖ := by positivity
      nlinarith [mul_nonneg (sub_nonneg.mpr hnorm)
        (add_nonneg (norm_nonneg u) hsum_nonneg)]
    have hsum_sq : (‖u - v‖ + ‖v‖) ^ 2 ≤
        2 * (‖u - v‖ ^ 2 + ‖v‖ ^ 2) := by
      nlinarith [sq_nonneg (‖u - v‖ - ‖v‖)]
    unfold bracketSq
    nlinarith [mul_nonneg (sq_nonneg (‖u - v‖)) (sq_nonneg (‖v‖))]
  have hratio : bracketSq x / bracketSq y ≤ 2 * bracketSq (x - y) := by
    rw [div_le_iff₀ (hbracket_pos y)]
    nlinarith [hbase x y]
  have hratio' : bracketSq y / bracketSq x ≤ 2 * bracketSq (x - y) := by
    rw [div_le_iff₀ (hbracket_pos x)]
    have hswap := hbase y x
    have hnorm : ‖y - x‖ = ‖x - y‖ := (norm_sub_rev x y).symm
    unfold bracketSq at hswap ⊢
    rw [hnorm] at hswap
    nlinarith [hswap]
  have hratio_nonneg : 0 ≤ bracketSq x / bracketSq y :=
    div_nonneg (le_of_lt (hbracket_pos x)) (le_of_lt (hbracket_pos y))
  have hratio'_nonneg : 0 ≤ bracketSq y / bracketSq x :=
    div_nonneg (le_of_lt (hbracket_pos y)) (le_of_lt (hbracket_pos x))
  have hright_pos : 0 < 2 * bracketSq (x - y) :=
    mul_pos (by norm_num) (hbracket_pos (x - y))
  by_cases hs : 0 ≤ s
  · simpa [abs_of_nonneg hs] using
      (Real.rpow_le_rpow (z := s / 2) hratio_nonneg hratio (by linarith))
  · have hneg : 0 < -s := by linarith
    have hpow :
        (bracketSq y / bracketSq x) ^ ((-s) / 2) ≤
          (2 * bracketSq (x - y)) ^ ((-s) / 2) :=
      Real.rpow_le_rpow (z := (-s) / 2) hratio'_nonneg hratio' (by positivity)
    have hflip :
        (bracketSq x / bracketSq y) ^ (s / 2) =
          (bracketSq y / bracketSq x) ^ ((-s) / 2) := by
      rw [show s / 2 = -((-s) / 2) by ring,
        Real.rpow_neg hratio_nonneg]
      rw [Real.div_rpow (le_of_lt (hbracket_pos x))
        (le_of_lt (hbracket_pos y))]
      rw [Real.div_rpow (le_of_lt (hbracket_pos y))
        (le_of_lt (hbracket_pos x))]
      have hxpow : bracketSq x ^ ((-s) / 2) ≠ 0 :=
        (Real.rpow_pos_of_pos (hbracket_pos x) _).ne'
      have hypow : bracketSq y ^ ((-s) / 2) ≠ 0 :=
        (Real.rpow_pos_of_pos (hbracket_pos y) _).ne'
      field_simp
    have habs : |s| = -s := abs_of_neg (lt_of_not_ge hs)
    rw [hflip, habs]
    exact hpow

private theorem rpow_sub_bound_ordered {a b σ : ℝ} (ha : 0 < a) (hab : a ≤ b) :
    |b ^ σ - a ^ σ| ≤ |σ| * |b - a| * (a ^ (σ - 1) + b ^ (σ - 1)) := by
  by_cases hlt : a < b
  · have hcont : ContinuousOn (fun t : ℝ => t ^ σ) (Set.Icc a b) := by
      intro t ht
      exact (Real.continuousAt_rpow_const t σ
        (Or.inl (ne_of_gt (lt_of_lt_of_le ha ht.1)))).continuousWithinAt
    have hderiv : ∀ t ∈ Set.Ioo a b,
        HasDerivAt (fun t : ℝ => t ^ σ) (σ * t ^ (σ - 1)) t := by
      intro t ht
      exact Real.hasDerivAt_rpow_const
        (Or.inl (ne_of_gt (lt_trans ha ht.1)))
    obtain ⟨c, hc, hmvt⟩ := exists_hasDerivAt_eq_slope
      (fun t : ℝ => t ^ σ) (fun t : ℝ => σ * t ^ (σ - 1)) hlt hcont hderiv
    have hcpos : 0 < c := lt_trans ha hc.1
    have hbpos : 0 < b := lt_of_lt_of_le ha hab
    have hmid : c ^ (σ - 1) ≤ a ^ (σ - 1) + b ^ (σ - 1) := by
      by_cases hq : 0 ≤ σ - 1
      · calc
          c ^ (σ - 1) ≤ b ^ (σ - 1) :=
            Real.rpow_le_rpow hcpos.le (le_of_lt hc.2) hq
          _ ≤ a ^ (σ - 1) + b ^ (σ - 1) :=
            le_add_of_nonneg_left (Real.rpow_nonneg ha.le _)
      · calc
          c ^ (σ - 1) ≤ a ^ (σ - 1) :=
            Real.rpow_le_rpow_of_nonpos ha (le_of_lt hc.1) (le_of_not_ge hq)
          _ ≤ a ^ (σ - 1) + b ^ (σ - 1) :=
            le_add_of_nonneg_right (Real.rpow_nonneg hbpos.le _)
    have hvalue : b ^ σ - a ^ σ = (b - a) * (σ * c ^ (σ - 1)) := by
      calc
        b ^ σ - a ^ σ = (b - a) * ((b ^ σ - a ^ σ) / (b - a)) := by
          have hcancel : (b ^ σ - a ^ σ) / (b - a) * (b - a) =
              b ^ σ - a ^ σ := div_mul_cancel₀ _ (sub_ne_zero.mpr (ne_of_gt hlt))
          calc
            b ^ σ - a ^ σ = (b ^ σ - a ^ σ) / (b - a) * (b - a) := hcancel.symm
            _ = (b - a) * ((b ^ σ - a ^ σ) / (b - a)) := by ring
        _ = (b - a) * (σ * c ^ (σ - 1)) := by rw [← hmvt]
    have hpowpos : 0 < c ^ (σ - 1) := Real.rpow_pos_of_pos (lt_trans ha hc.1) _
    have habs : |b ^ σ - a ^ σ| = |σ| * |b - a| * c ^ (σ - 1) := by
      rw [hvalue, abs_mul, abs_mul, abs_of_pos hpowpos]
      ring
    calc
      |b ^ σ - a ^ σ| = |σ| * |b - a| * c ^ (σ - 1) := habs
      _ ≤ |σ| * |b - a| * (a ^ (σ - 1) + b ^ (σ - 1)) :=
        mul_le_mul_of_nonneg_left hmid (by positivity)
  · have hab' : a = b := le_antisymm hab (le_of_not_gt hlt)
    subst b
    simp

theorem rpowDifferenceBound {a b σ : ℝ} (ha : 0 < a) (hb : 0 < b) :
    |a ^ σ - b ^ σ| ≤ |σ| * |a - b| * (a ^ (σ - 1) + b ^ (σ - 1)) := by
  by_cases hab : a ≤ b
  · simpa [abs_sub_comm] using rpow_sub_bound_ordered ha hab
  · have hba : b ≤ a := le_of_not_ge hab
    simpa [abs_sub_comm, add_comm] using rpow_sub_bound_ordered hb hba

theorem japBracketLipschitz {E : Type*} [NormedAddCommGroup E] (x y : E) :
    |japBracket x - japBracket y| ≤ ‖x - y‖ := by
  let a := ‖x‖
  let b := ‖y‖
  let A := Real.sqrt (1 + a ^ 2)
  let B := Real.sqrt (1 + b ^ 2)
  have ha : 0 ≤ a := norm_nonneg x
  have hb : 0 ≤ b := norm_nonneg y
  have hApos : 0 < A := Real.sqrt_pos.2 (by positivity)
  have hBpos : 0 < B := Real.sqrt_pos.2 (by positivity)
  have hA_sq : A ^ 2 = 1 + a ^ 2 := by
    dsimp [A]
    rw [Real.sq_sqrt]
    positivity
  have hB_sq : B ^ 2 = 1 + b ^ 2 := by
    dsimp [B]
    rw [Real.sq_sqrt]
    positivity
  have haA : a ≤ A := by
    dsimp [A]
    apply Real.le_sqrt_of_sq_le
    nlinarith
  have hbB : b ≤ B := by
    dsimp [B]
    apply Real.le_sqrt_of_sq_le
    nlinarith
  have hsum : a + b ≤ A + B := add_le_add haA hbB
  have hsum_pos : 0 < A + B := add_pos hApos hBpos
  have hfactor : (A - B) * (A + B) = (a - b) * (a + b) := by
    nlinarith [hA_sq, hB_sq]
  have hprod : |A - B| * (A + B) = |a - b| * (a + b) := by
    calc
      |A - B| * (A + B) = |(A - B) * (A + B)| := by
        rw [abs_mul, abs_of_pos hsum_pos]
      _ = |(a - b) * (a + b)| := by rw [hfactor]
      _ = |a - b| * (a + b) := by
        rw [abs_mul, abs_of_nonneg (add_nonneg ha hb)]
  have hmul : |A - B| * (A + B) ≤ |a - b| * (A + B) := by
    rw [hprod]
    exact mul_le_mul_of_nonneg_left hsum (abs_nonneg (a - b))
  have hbound : |A - B| ≤ |a - b| := le_of_mul_le_mul_right hmul hsum_pos
  have hjap : |japBracket x - japBracket y| = |A - B| := by
    simp [japBracket, bracketSq, A, B, a, b]
  calc
    |japBracket x - japBracket y| = |A - B| := hjap
    _ ≤ |a - b| := hbound
    _ ≤ ‖x - y‖ := abs_norm_sub_norm_le x y

/-- Global endpoint difference bound for scalar Bessel weights. -/
theorem besselWeightDifference {N : ℕ} (ξ η : Carrier N) (σ : ℝ) :
    |japBracket ξ ^ σ - japBracket η ^ σ| ≤
      |σ| * ‖ξ - η‖ *
        (japBracket ξ ^ (σ - 1) + japBracket η ^ (σ - 1)) := by
  calc
    |japBracket ξ ^ σ - japBracket η ^ σ| ≤
        |σ| * |japBracket ξ - japBracket η| *
          (japBracket ξ ^ (σ - 1) + japBracket η ^ (σ - 1)) :=
      rpowDifferenceBound (Real.sqrt_pos.2 (hbracket_pos _))
        (Real.sqrt_pos.2 (hbracket_pos _))
    _ ≤ |σ| * ‖ξ - η‖ *
          (japBracket ξ ^ (σ - 1) + japBracket η ^ (σ - 1)) := by
      have hjx : 0 < japBracket ξ := Real.sqrt_pos.2 (hbracket_pos ξ)
      have hjy : 0 < japBracket η := Real.sqrt_pos.2 (hbracket_pos η)
      have hsum : 0 ≤ japBracket ξ ^ (σ - 1) + japBracket η ^ (σ - 1) := by
        positivity
      exact mul_le_mul_of_nonneg_right
        (mul_le_mul_of_nonneg_left (japBracketLipschitz ξ η) (abs_nonneg σ))
        hsum
  where
    hbracket_pos (z : Carrier N) : 0 < bracketSq z := by
      unfold bracketSq
      positivity

end Hormander.B

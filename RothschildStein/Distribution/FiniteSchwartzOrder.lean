-- Copyright (c) 2026 Scott Armstrong and Amélie Loher. All rights reserved.
-- Released under Apache 2.0 license as described in the file LICENSE.
module

public import RothschildStein.Distribution.SchwartzSobolevMonotone
public import Mathlib.Analysis.SpecialFunctions.Trigonometric.Basic

set_option autoImplicit false
set_option relaxedAutoImplicit false
set_option backward.isDefEq.respectTransparency false
@[expose] public section
noncomputable section
open MeasureTheory SchwartzMap
open scoped FourierTransform BigOperators
namespace RothschildStein.Distribution

/-- every derivative seminorm through order m is
bounded by a single explicit H^(m+s) norm. -/
theorem schwartzSeminorm_zero_le_sobolev {N : ℕ} (m n : ℕ) (hn : n ≤ m) (s : ℝ)
    (hs : (N : ℝ) < 2 * s) (φ : 𝓢(Hormander.A.Carrier N, ℂ)) :
    SchwartzMap.seminorm ℂ 0 n φ ≤ (2 * Real.pi) ^ m *
      ‖(Hormander.A.memLp_bessel_weight hs).toLp
        (fun ξ : Hormander.A.Carrier N => (1 + ‖ξ‖ ^ 2) ^ (-s / 2))‖ *
      ‖Hormander.A.schwartzToSobolev ((m : ℝ) + s) φ‖ := by
  apply SchwartzMap.seminorm_le_bound ℂ 0 n φ (by positivity)
  intro x
  simp only [pow_zero, one_mul]
  have h := norm_iteratedFDeriv_le_sobolev n s hs φ x
  have hpow : (2 * Real.pi) ^ n ≤ (2 * Real.pi) ^ m :=
    pow_le_pow_right₀ (by nlinarith [Real.two_le_pi]) hn
  have hnorm := schwartzSobolev_norm_mono (N := N)
    (show (n : ℝ) + s ≤ (m : ℝ) + s by
      have hnm : (n : ℝ) ≤ (m : ℝ) := by exact_mod_cast hn
      linarith) φ
  exact h.trans (mul_le_mul (mul_le_mul_of_nonneg_right hpow (norm_nonneg _)) hnorm
    (norm_nonneg _) (by positivity))

/-- any tempered distribution with a finite sum
of unweighted Schwartz derivative-seminorm bounds has negative
Sobolev order m+s for every s>N/2. -/
theorem memSobolev_neg_of_finiteSchwartzOrder {N : ℕ} (m : ℕ) (s : ℝ)
    (hs : (N : ℝ) < 2 * s) (v : 𝓢'(Hormander.A.Carrier N, ℂ))
    {C : ℝ} (hC : 0 ≤ C)
    (h : ∀ φ : 𝓢(Hormander.A.Carrier N, ℂ), ‖v φ‖ ≤
      C * ∑ n ∈ Finset.range (m + 1), SchwartzMap.seminorm ℂ 0 n φ) :
    TemperedDistribution.MemSobolev (-((m : ℝ) + s)) 2 v := by
  let W : ℝ := ‖(Hormander.A.memLp_bessel_weight hs).toLp
    (fun ξ : Hormander.A.Carrier N => (1 + ‖ξ‖ ^ 2) ^ (-s / 2))‖
  let D : ℝ := C * (m + 1 : ℕ) * ((2 * Real.pi) ^ m * W)
  have hD : 0 ≤ D := by dsimp [D, W]; positivity
  apply memSobolev_neg_of_schwartz_dualityBound ((m : ℝ) + s)
    (by linarith [show (0 : ℝ) ≤ N from Nat.cast_nonneg N,
      show (0 : ℝ) ≤ m from Nat.cast_nonneg m]) v hD
  intro φ
  rw [weightedFourier_norm]
  have hsum : (∑ n ∈ Finset.range (m + 1), SchwartzMap.seminorm ℂ 0 n φ) ≤
      (m + 1 : ℕ) * ((2 * Real.pi) ^ m * W * ‖Hormander.A.schwartzToSobolev ((m : ℝ) + s) φ‖) := by
    calc
      _ ≤ ∑ n ∈ Finset.range (m + 1), ((2 * Real.pi) ^ m * W *
          ‖Hormander.A.schwartzToSobolev ((m : ℝ) + s) φ‖) := by
        apply Finset.sum_le_sum
        intro n hn
        exact schwartzSeminorm_zero_le_sobolev m n (Finset.mem_range_succ_iff.mp hn) s hs φ
      _ = _ := by simp
  exact (h φ).trans ((mul_le_mul_of_nonneg_left hsum hC).trans_eq (by dsimp [D]; ring))

end RothschildStein.Distribution

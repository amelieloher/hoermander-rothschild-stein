-- Copyright (c) 2026 Scott Armstrong and Amélie Loher. All rights reserved.
-- Released under Apache 2.0 license as described in the file LICENSE.
module

public import RothschildStein.H2.KreinGrowth
public import Mathlib.Analysis.InnerProductSpace.Symmetric

set_option autoImplicit false
set_option relaxedAutoImplicit false

@[expose] public section
noncomputable section

namespace RothschildStein.H2
variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℝ H]

/-- Cauchy–Schwarz for a symmetric linear map, BB pp. 309–310. -/
theorem symmetric_norm_sq_le (S : H →ₗ[ℝ] H) (hS : S.IsSymmetric) (y : H) :
    ‖S y‖ ^ 2 ≤ ‖y‖ * ‖S (S y)‖ := by
  rw [← real_inner_self_eq_norm_sq]
  rw [hS]
  exact real_inner_le_norm _ _

/-- An auxiliary seminorm bound controls powers of a linear map. -/
theorem seminorm_pow_bound (N : Seminorm ℝ H) (S : H →ₗ[ℝ] H)
    {c : ℝ} (hc : 0 ≤ c) (hb : ∀ y, N (S y) ≤ c * N y) (n : ℕ) (y : H) :
    N ((S ^ n) y) ≤ c ^ n * N y := by
  induction n with
  | zero => simp
  | succ n ih =>
    rw [pow_succ', Module.End.mul_apply]
    exact (hb _).trans (by simpa only [pow_succ, mul_assoc, mul_comm c] using
      mul_le_mul_of_nonneg_left ih hc)

/-- A symmetric map bounded in a dominating auxiliary seminorm has
its same bound in the inner-product norm. BB Thm 7.20, pp. 309–310. -/
theorem symmetric_norm_bound (N : Seminorm ℝ H) (S : H →ₗ[ℝ] H) (hS : S.IsSymmetric)
    {k c : ℝ} (hk : 0 ≤ k) (hc : 0 ≤ c)
    (hdom : ∀ y, ‖y‖ ≤ k * N y) (hb : ∀ y, N (S y) ≤ c * N y) (y : H) :
    ‖S y‖ ≤ c * ‖y‖ := by
  by_cases hy : y = 0
  · simp [hy]
  have hym : 0 < ‖y‖ := norm_pos_iff.mpr hy
  let v : ℕ → ℝ := fun j => ‖(S ^ (2 ^ j)) y‖ / ‖y‖
  have hv : ∀ j, 0 ≤ v j := fun j => div_nonneg (norm_nonneg _) hym.le
  have hs : ∀ j, v j ^ 2 ≤ v (j + 1) := by
    intro j
    have he := symmetric_norm_sq_le (S ^ (2 ^ j)) (hS.pow _) y
    have hid : (S ^ (2 ^ j)) ((S ^ (2 ^ j)) y) = (S ^ (2 ^ (j + 1))) y := by
      rw [pow_succ, pow_mul, pow_two, Module.End.mul_apply]
    rw [hid] at he
    dsimp [v]
    rw [div_pow, div_le_div_iff₀ (pow_pos hym 2) hym]
    nlinarith
  have hb' : ∀ j, v j ≤ (k * N y / ‖y‖) * c ^ (2 ^ j) := by
    intro j
    have he := (hdom ((S ^ (2 ^ j)) y)).trans
      (mul_le_mul_of_nonneg_left (seminorm_pow_bound N S hc hb _ y) hk)
    dsimp [v]
    apply (div_le_iff₀ hym).mpr
    calc
      _ ≤ k * (c ^ (2 ^ j) * N y) := he
      _ = _ := by field_simp
  have he := krein_dyadic_growth hv hc hs hb'
  dsimp [v] at he
  simpa only [pow_zero, pow_one] using (div_le_iff₀ hym).mp he

end RothschildStein.H2

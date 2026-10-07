-- Copyright (c) 2026 Scott Armstrong and Amélie Loher. All rights reserved.
-- Released under Apache 2.0 license as described in the file LICENSE.
module

public import RothschildStein.G4.WeightedChartTangent
public import RothschildStein.G4.WeightedBoxSegments

@[expose] public section
set_option autoImplicit false
set_option relaxedAutoImplicit false
noncomputable section
open Set

namespace RothschildStein.G4

/-- A single small factor below the largest-weight threshold
controls every positive coordinate weight (BB Prop 9.55, p. 457). -/
theorem weighted_control_cost_from_linear_bound {n s : ℕ} (w : Fin n → ℕ+)
    (hw : ∀ i, (w i : ℕ) ≤ s) {C d r : ℝ}
    (hd : 0 ≤ d) (hd1 : d ≤ 1) (hr : 0 ≤ r) (hC : C ≤ d ^ s)
    {c : Fin n → ℝ} (hc : ∀ i, |c i| ≤ C * r ^ (w i : ℕ)) :
    ∀ i, |c i| ≤ (d * r) ^ (w i : ℕ) := by
  intro i
  rw [mul_pow]
  exact (hc i).trans (mul_le_mul_of_nonneg_right
    (hC.trans (pow_le_pow_of_le_one hd hd1 (hw i))) (pow_nonneg hr _))

/-- A dimension-small derivative error gives a factor-three
linear control bound for every contraction segment, at the original radius. -/
theorem contraction_tangent_control_bound {n : ℕ} (w : Fin n → ℕ+)
    (E : Matrix (Fin n) (Fin n) ℝ) {β r κ : ℝ}
    (hβ : 0 ≤ β) (hβ1 : β ≤ 1) (hr : 0 < r) (hκ : 0 ≤ κ)
    (hsmall : (n : ℝ) * κ ≤ 1 / 4)
    (hE : ∀ j i, |E j i| ≤ κ * r ^ (((w j : ℕ) : ℤ) - ((w i : ℕ) : ℤ)))
    {u v : Fin n → ℝ} (hu : u ∈ weightedBox w (β * r))
    (hv : v ∈ weightedBox w (β * r)) :
    ∀ j, |(v - u) j + E.mulVec (v - u) j| ≤ 3 * β * r ^ (w j : ℕ) := by
  have hh := weightedBox_segment_velocity_bound w hβ hβ1 hr.le hu hv
  have hc := weighted_tangent_control_bound w E (v - u) hr hκ
    (show 0 ≤ 2 * β by positivity) hE hh
  intro j
  exact (hc j).trans (mul_le_mul_of_nonneg_right
    (by nlinarith : (1 + (n : ℝ) * κ) * (2 * β) ≤ 3 * β) (pow_nonneg hr.le _))

end RothschildStein.G4

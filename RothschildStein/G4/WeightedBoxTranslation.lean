-- Copyright (c) 2026 Scott Armstrong and Amélie Loher. All rights reserved.
-- Released under Apache 2.0 license as described in the file LICENSE.
module

public import RothschildStein.G4.WeightedBoxes

@[expose] public section
set_option autoImplicit false
set_option relaxedAutoImplicit false
noncomputable section
open Set

namespace RothschildStein.G4

/-- Addition of strict weighted boxes respects the sum of their
positive radii (BB Prop 9.55, pp. 457–458). -/
theorem weightedBox_add_mem {n : ℕ} (w : Fin n → ℕ+)
    {a b : ℝ} (ha : 0 ≤ a) (hb : 0 ≤ b)
    {u v : Fin n → ℝ} (hu : u ∈ weightedBox w a)
    (hv : v ∈ weightedBox w b) : u + v ∈ weightedBox w (a + b) := by
  intro i
  calc
    |(u + v) i| ≤ |u i| + |v i| := abs_add_le _ _
    _ < a ^ (w i : ℕ) + b ^ (w i : ℕ) := add_lt_add (hu i) (hv i)
    _ ≤ (a + b) ^ (w i : ℕ) := pow_add_pow_le ha hb (w i).ne_zero

/-- Translating a half-size coordinate box by a point in the
quarter-size box stays inside the original chart domain. -/
theorem weightedBox_half_add_quarter_mem {n : ℕ} (w : Fin n → ℕ+)
    {a r : ℝ} (ha : 0 ≤ a) (hr : 0 ≤ r)
    {u v : Fin n → ℝ} (hu : u ∈ weightedBox w (a / 2 * r))
    (hv : v ∈ weightedBox w (a / 4 * r)) : u + v ∈ weightedBox w (a * r) := by
  have h := weightedBox_add_mem w (by positivity) (by positivity) hu hv
  intro i
  exact (h i).trans_le (pow_le_pow_left₀ (by positivity)
    (by nlinarith : a / 2 * r + a / 4 * r ≤ a * r) _)

end RothschildStein.G4

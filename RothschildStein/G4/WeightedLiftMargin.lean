-- Copyright (c) 2026 Scott Armstrong and Amélie Loher. All rights reserved.
-- Released under Apache 2.0 license as described in the file LICENSE.
module

public import RothschildStein.G4.WeightedBoxes
public import Mathlib.Analysis.SpecialFunctions.Pow.Real

@[expose] public section
set_option autoImplicit false
set_option relaxedAutoImplicit false
noncomputable section

namespace RothschildStein.G4

/-- A numerical short-path radius leaves the explicit half-box
margin used by the continuation proof (BB Prop 9.52, pp. 448–449). -/
theorem exists_weighted_lift_margin (s : ℕ) {a C : ℝ}
    (ha : 0 < a) (ha1 : a ≤ 1) (hC : 0 ≤ C) :
    ∃ b : ℝ, 0 < b ∧ b < a / 4 ∧ 2 * b ≤ 1 ∧ C * b < (a / 2) ^ s / 4 := by
  let b := min (a / 8) ((a / 2) ^ s / (8 * (1 + C)))
  have hb : 0 < b := lt_min (by positivity) (by positivity)
  have hba : b ≤ a / 8 := min_le_left _ _
  have hbC : b ≤ (a / 2) ^ s / (8 * (1 + C)) := min_le_right _ _
  have hprod : b * (8 * (1 + C)) ≤ (a / 2) ^ s :=
    (le_div_iff₀ (by positivity)).mp hbC
  refine ⟨b, hb, (hba.trans_lt (by linarith)), (by linarith), ?_⟩
  have hp : 0 < (a / 2) ^ s := by positivity
  nlinarith

/-- The margin at the maximal weight gives strict interior in
every coordinate of the half-box, with a factor-four clearance retained
(BB Prop 9.52, (9.51), pp. 448–449). -/
theorem weighted_lift_mem_halfBox {n s : ℕ} (w : Fin n → ℕ+)
    (hw : ∀ i, (w i : ℕ) ≤ s) {a b C r : ℝ}
    (ha : 0 < a) (ha1 : a ≤ 1) (hr : 0 < r) (hmargin : C * b < (a / 2) ^ s / 4)
    (u : Fin n → ℝ) (hu : ∀ i, |u i| ≤ C * b * r ^ (w i : ℕ)) :
    u ∈ weightedBox w (a * r / 2) := by
  intro i
  have hbase : 0 ≤ a / 2 := by positivity
  have hbase1 : a / 2 ≤ 1 := by linarith
  have hp : (a / 2) ^ s ≤ (a / 2) ^ (w i : ℕ) :=
    pow_le_pow_of_le_one hbase hbase1 (hw i)
  have hwpos : 0 < (a / 2) ^ (w i : ℕ) := by positivity
  have hcoeff : C * b < (a / 2) ^ (w i : ℕ) := by linarith
  calc
    |u i| ≤ C * b * r ^ (w i : ℕ) := hu i
    _ < (a / 2) ^ (w i : ℕ) * r ^ (w i : ℕ) :=
      mul_lt_mul_of_pos_right hcoeff (pow_pos hr _)
    _ = (a * r / 2) ^ (w i : ℕ) := by rw [← mul_pow]; congr 1; ring

end RothschildStein.G4

-- Copyright (c) 2026 Scott Armstrong and Amélie Loher. All rights reserved.
-- Released under Apache 2.0 license as described in the file LICENSE.
module

public import RothschildStein.G1.MixedFlowJets

@[expose] public section
set_option autoImplicit false
set_option relaxedAutoImplicit false
noncomputable section
open scoped BigOperators

namespace RothschildStein.G1

/-- The finite-jet rate is linear in the coefficient bound
(BB Prop 1.2, pp. 3–4). -/
theorem spatialJetRate_mul_left (r : ℕ) (a B : ℝ) :
    spatialJetRate r (a * B) = a * spatialJetRate r B := by
  unfold spatialJetRate
  rw [Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro i hi
  ring

/-- An explicit positive smaller time scale satisfies the
mixed-jet bootstrap condition for any finite coefficient norm
(BB Prop 1.2, pp. 3–4). -/
theorem exists_mixedJet_time_scale {τ B : ℝ} (hτ : 0 < τ) (hB : 0 ≤ B) (r : ℕ) :
    ∃ ε : ℝ, 0 < ε ∧ 4 * ε < τ ∧
      spatialJetRate r (ε * 2 ^ r * r.factorial * B) < 1 := by
  let C : ℝ := 2 ^ r * r.factorial * B
  let R : ℝ := spatialJetRate r C
  have hC : 0 ≤ C := by dsimp [C]; positivity
  have hR : 0 ≤ R := by
    dsimp [R, spatialJetRate]
    exact Finset.sum_nonneg (fun i _ => by positivity)
  let ε : ℝ := min (τ / 8) (1 / (2 * (1 + R)))
  have hε : 0 < ε := lt_min (by positivity) (by positivity)
  have hετ : 4 * ε < τ := by
    have hm : ε ≤ τ / 8 := min_le_left _ _
    linarith
  refine ⟨ε, hε, hετ, ?_⟩
  have heq : ε * 2 ^ r * r.factorial * B = ε * C := by dsimp [C]; ring
  rw [heq, spatialJetRate_mul_left]
  change ε * R < 1
  have hm : ε ≤ 1 / (2 * (1 + R)) := min_le_right _ _
  have hden : 0 < 2 * (1 + R) := by positivity
  have hprod : ε * (2 * (1 + R)) ≤ 1 := (le_div_iff₀ hden).mp hm
  nlinarith

end RothschildStein.G1

-- Copyright (c) 2026 Scott Armstrong and Amélie Loher. All rights reserved.
-- Released under Apache 2.0 license as described in the file LICENSE.
module

public import RothschildStein.G4.WeightedPartialLiftExtension

@[expose] public section
set_option autoImplicit false
set_option relaxedAutoImplicit false
noncomputable section
open Set Metric

namespace RothschildStein.G4

/-- A common weighted coordinate variation bound gives the
Euclidean Lipschitz bound, and hence absolute continuity, on every
partial time interval (BB Prop 9.52, p. 449). -/
theorem weighted_variation_lipschitzOn {n : ℕ} (w : Fin n → ℕ+)
    {r T C : ℝ} (hr : 0 < r) (hr1 : r ≤ 1) (hC : 0 ≤ C)
    (θ : ℝ → (Fin n → ℝ))
    (hvariation : ∀ σ ∈ Icc (0 : ℝ) T, ∀ τ ∈ Icc (0 : ℝ) T, ∀ i,
      |θ τ i - θ σ i| ≤ C * r ^ (w i : ℕ) * |τ - σ|) :
    LipschitzOnWith ⟨C, hC⟩ θ (Icc (0 : ℝ) T) := by
  apply LipschitzOnWith.of_dist_le_mul
  intro σ hσ τ hτ
  apply (dist_pi_le_iff (mul_nonneg hC dist_nonneg)).mpr
  intro i
  have hp : r ^ (w i : ℕ) ≤ 1 := pow_le_one₀ hr.le hr1
  have hh := hvariation τ hτ σ hσ i
  rw [Real.dist_eq, Real.dist_eq]
  exact hh.trans (mul_le_mul_of_nonneg_right
    (mul_le_of_le_one_right hC hp) (abs_nonneg _))

end RothschildStein.G4

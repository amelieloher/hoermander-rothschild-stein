-- Copyright (c) 2026 Scott Armstrong and Amélie Loher. All rights reserved.
-- Released under Apache 2.0 license as described in the file LICENSE.
module

public import RothschildStein.G1.JetBounds
public import RothschildStein.G4.TimeOneFlow

@[expose] public section
set_option autoImplicit false
set_option relaxedAutoImplicit false
noncomputable section
open Set Metric
open scoped BigOperators NNReal

namespace RothschildStein.G4

/-- Smooth finite field families have a common convex local buffer,
with coefficient and Lipschitz budgets on that same buffer. -/
theorem exists_local_field_buffer {m n : ℕ} {Ω : Set (Fin n → ℝ)}
    (hΩ : IsOpen Ω) {Z : Fin m → (Fin n → ℝ) → (Fin n → ℝ)}
    (hZ : ∀ i, ContDiffOn ℝ (⊤ : ℕ∞) (Z i) Ω)
    {x₀ : Fin n → ℝ} (hx₀ : x₀ ∈ Ω) :
    ∃ R : ℝ, 0 < R ∧ closedBall x₀ R ⊆ Ω ∧ ∃ P : ℝ, 0 < P ∧
      (∀ i, LipschitzOnWith (Real.toNNReal P) (Z i) (ball x₀ R)) ∧
      ∀ z ∈ closedBall x₀ R, ∑ i, ‖Z i z‖ ≤ m * P := by
  obtain ⟨d, hd, hball⟩ := Metric.mem_nhds_iff.mp (hΩ.mem_nhds hx₀)
  let R := d / 2
  have hR : 0 < R := half_pos hd
  have hRΩ : closedBall x₀ R ⊆ Ω :=
    (closedBall_subset_ball (half_lt_self hd)).trans hball
  obtain ⟨P, hP, hbound⟩ := G1.exists_uniform_coefficient_jet_bound
    hΩ (isCompact_closedBall x₀ R) hRΩ Z hZ 1
  refine ⟨R, hR, hRΩ, P, hP, ?_, ?_⟩
  · intro i
    apply (convex_ball x₀ R).lipschitzOnWith_of_nnnorm_fderiv_le (𝕜 := ℝ)
    · intro z hz
      exact ((hZ i).contDiffAt (hΩ.mem_nhds (hRΩ (ball_subset_closedBall hz)))).differentiableAt
        (by simp)
    · intro z hz
      apply NNReal.coe_le_coe.mp
      rw [Real.coe_toNNReal _ hP.le]
      change ‖fderiv ℝ (Z i) z‖ ≤ P
      have hb := hbound i 1 le_rfl z (ball_subset_closedBall hz)
      rw [norm_iteratedFDerivWithin_one (Z i) (hΩ.uniqueDiffOn _
        (hRΩ (ball_subset_closedBall hz))), fderivWithin_of_isOpen hΩ
        (hRΩ (ball_subset_closedBall hz))] at hb
      exact hb
  · intro z hz
    calc
      _ ≤ ∑ i : Fin m, P := by
        apply Finset.sum_le_sum
        intro i hi
        simpa using hbound i 0 (by omega) z hz
      _ = m * P := by simp

end RothschildStein.G4

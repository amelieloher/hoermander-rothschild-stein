-- Copyright (c) 2026 Scott Armstrong and Amélie Loher. All rights reserved.
-- Released under Apache 2.0 license as described in the file LICENSE.
module
public import RothschildStein.G4.FirstExit
public import Mathlib.Analysis.Normed.Group.Bounded
@[expose] public section
set_option autoImplicit false
set_option relaxedAutoImplicit false
noncomputable section
open Set Metric
open scoped BigOperators
namespace RothschildStein.G4

/-- Numerical coefficient bounds and first exit retain every small controlled
curve in the larger original-domain buffer. -/
theorem exists_numerical_controlled_curve_buffer {m n : ℕ}
    (R P : ℝ) (hR : 0 < R) :
    ∃ η : ℝ, 0 < η ∧ η ≤ 1 ∧ ∀ (Ω : Set (Fin n → ℝ)) (w : Fin m → ℕ+)
      (Z : Fin m → (Fin n → ℝ) → (Fin n → ℝ)) (z : Fin n → ℝ),
      (∀ i y, y ∈ closedBall z R → ‖Z i y‖ ≤ P) →
      ∀ δ : ℝ, δ < η →
      ∀ γ : ℝ → (Fin n → ℝ), isControlledCurve Ω w Z δ γ →
      γ 0 ∈ closedBall z (R/2) → MapsTo γ (Icc 0 1) (closedBall z R) := by
  classical
  let B := max 1 ((m : ℝ)*P)
  have hB : 0 < B := zero_lt_one.trans_le (le_max_left _ _)
  let η := min 1 (R / (4*B))
  have hη : 0 < η := lt_min zero_lt_one (div_pos hR (by positivity))
  refine ⟨η, hη, min_le_left _ _, ?_⟩
  intro Ω w Z z hZ δ hδ γ hγ hx t ht
  have hsmall : δ * B < R/2 := by
    have hh : δ < R/(4*B) := hδ.trans_le (min_le_right _ _)
    have hh' := (lt_div_iff₀ (by positivity : 0 < 4*B)).mp hh
    nlinarith
  have hbound : ∀ y, ‖y - γ 0‖ ≤ R/2 → ∑ i, ‖Z i y‖ ≤ B := by
    intro y hy
    have hyR : y ∈ closedBall z R := by
      rw [mem_closedBall, dist_eq_norm] at hx ⊢
      calc
        ‖y-z‖ ≤ ‖y-γ 0‖ + ‖γ 0-z‖ := norm_sub_le_norm_sub_add_norm_sub _ _ _
        _ ≤ R := by linarith
    calc
      ∑ i, ‖Z i y‖ ≤ ∑ _i : Fin m, P := Finset.sum_le_sum (fun i _ => hZ i y hyR)
      _ = (m : ℝ)*P := by simp
      _ ≤ B := le_max_right _ _
  have hs := controlledCurve_stays_ball hγ (hδ.le.trans (min_le_left _ _))
    hB.le (by positivity : 0 < R/2) hsmall hbound t ht
  rw [mem_closedBall, dist_eq_norm] at hx ⊢
  have hs' : ‖γ t - γ 0‖ < R/2 := by simpa only [mem_ball, dist_eq_norm] using hs
  calc
    ‖γ t-z‖ ≤ ‖γ t-γ 0‖ + ‖γ 0-z‖ := norm_sub_le_norm_sub_add_norm_sub _ _ _
    _ ≤ R := by linarith
end RothschildStein.G4

-- Copyright (c) 2026 Scott Armstrong and Amélie Loher. All rights reserved.
-- Released under Apache 2.0 license as described in the file LICENSE.
module

public import Mathlib

/-! Rational cylinders containing two nearby space-time points. -/

set_option autoImplicit false
set_option relaxedAutoImplicit false
@[expose] public section
open Set Metric
namespace HeatKernel

/-- Two nearby points below a fixed top time lie in a common cylinder with
rational top time and radius, and center in a prescribed dense sequence.
The chosen cylinder stays below the top time and below the supplied radius. -/
theorem exists_rational_cylinder_containing_pair
    {α : Type*} [PseudoMetricSpace α] (c : ℕ → α) (hc : DenseRange c)
    {t s top δ R : ℝ} {x y : α} (hδ : 0 < δ)
    (htop : max t s < top) (htime : |t - s| ≤ δ ^ 2)
    (hspace : dist x y ≤ δ) (hR : 16 * δ ≤ R) :
    ∃ (τ ρ : ℚ) (i : ℕ),
      max t s < (τ : ℝ) ∧ (τ : ℝ) < top ∧ (τ : ℝ) - max t s < δ ^ 2 ∧
      dist x (c i) < 2 * δ ∧ 4 * δ < (ρ : ℝ) ∧ (ρ : ℝ) < R ∧
      (t, x) ∈ Ioo ((τ : ℝ) - (ρ : ℝ) ^ 2) τ ×ˢ ball (c i) ρ ∧
      (s, y) ∈ Ioo ((τ : ℝ) - (ρ : ℝ) ^ 2) τ ×ˢ ball (c i) ρ := by
  have hδsq : 0 < δ ^ 2 := sq_pos_of_pos hδ
  obtain ⟨τ, hτlo, hτhi⟩ := exists_rat_btwn
    (lt_min htop (by linarith : max t s < max t s + δ ^ 2))
  have hτtop : (τ : ℝ) < top := hτhi.trans_le (min_le_left _ _)
  have hτnear : (τ : ℝ) - max t s < δ ^ 2 := by
    have := hτhi.trans_le (min_le_right _ _)
    linarith
  obtain ⟨i, hi⟩ := hc.exists_dist_lt x (by linarith : 0 < 2 * δ)
  obtain ⟨ρ, hρlo, hρhi⟩ := exists_rat_btwn (by linarith : 4 * δ < R)
  have hρpos : 0 < (ρ : ℝ) := by linarith
  have hsquares : 2 * δ ^ 2 < (ρ : ℝ) ^ 2 := by nlinarith
  have hmaxt : max t s - t ≤ δ ^ 2 := by
    rcases le_total t s with h | h
    · rw [max_eq_right h]
      have := (abs_le.mp htime).1
      linarith
    · rw [max_eq_left h]
      linarith
  have hmaxs : max t s - s ≤ δ ^ 2 := by
    rcases le_total t s with h | h
    · rw [max_eq_right h]
      linarith
    · rw [max_eq_left h]
      have := (abs_le.mp htime).2
      linarith
  have hy : dist y (c i) < (ρ : ℝ) := by
    have htri := dist_triangle y x (c i)
    rw [dist_comm y x] at htri
    linarith
  refine ⟨τ, ρ, i, hτlo, hτtop, hτnear, hi, hρlo, hρhi, ?_, ?_⟩
  · exact ⟨⟨by linarith, (le_max_left t s).trans_lt hτlo⟩, by
      change dist x (c i) < (ρ : ℝ)
      linarith⟩
  · exact ⟨⟨by linarith, (le_max_right t s).trans_lt hτlo⟩, hy⟩

end HeatKernel

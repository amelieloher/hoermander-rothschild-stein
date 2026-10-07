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

/-- Compact coefficient bounds retain every small controlled curve from the
quarter buffer inside the half buffer, uniformly over its centre. -/
theorem exists_compact_quarter_curve_buffer {m n : ℕ}
    {Ω : Set (Fin n → ℝ)} (w : Fin m → ℕ+)
    (Z : Fin m → (Fin n → ℝ) → (Fin n → ℝ))
    {z : Fin n → ℝ} {R : ℝ} (hR : 0 < R)
    (hZ : ∀ i, ContinuousOn (Z i) (closedBall z R)) :
    ∃ η : ℝ, 0 < η ∧ η ≤ 1 ∧ ∀ δ : ℝ, δ < η →
      ∀ γ : ℝ → (Fin n → ℝ), isControlledCurve Ω w Z δ γ →
      γ 0 ∈ closedBall z (R/4) → MapsTo γ (Icc 0 1) (closedBall z (R/2)) := by
  classical
  have hc : ContinuousOn (fun x => ∑ i, ‖Z i x‖) (closedBall z R) :=
    continuousOn_finsetSum _ (fun i _ => (hZ i).norm)
  obtain ⟨B₀, hb⟩ := ((isCompact_closedBall z R).image_of_continuousOn hc).isBounded.exists_norm_le
  let B := max 1 B₀
  have hB : 0 < B := lt_of_lt_of_le zero_lt_one (le_max_left _ _)
  let η := min 1 (R / (8*B))
  have hη : 0 < η := lt_min zero_lt_one (div_pos hR (by positivity))
  refine ⟨η, hη, min_le_left _ _, ?_⟩
  intro δ hδ γ hγ hx t ht
  have hsmall : δ * B < R/4 := by
    have hh : δ < R/(8*B) := hδ.trans_le (min_le_right _ _)
    have hh' := (lt_div_iff₀ (by positivity : 0 < 8*B)).mp hh
    nlinarith
  have hbound : ∀ y, ‖y - γ 0‖ ≤ R/4 → ∑ i, ‖Z i y‖ ≤ B := by
    intro y hy
    have hyR : y ∈ closedBall z R := by
      rw [mem_closedBall, dist_eq_norm] at hx ⊢
      calc
        ‖y-z‖ ≤ ‖y-γ 0‖ + ‖γ 0-z‖ := norm_sub_le_norm_sub_add_norm_sub _ _ _
        _ ≤ R := by linarith
    have hh := hb _ (mem_image_of_mem _ hyR)
    have hn : (∑ i, ‖Z i y‖) ≤ ‖(∑ i, ‖Z i y‖)‖ := by
      simpa only [Real.norm_eq_abs] using le_abs_self (∑ i, ‖Z i y‖)
    exact hn.trans (hh.trans (le_max_right _ _))
  have hs := controlledCurve_stays_ball hγ (hδ.le.trans (min_le_left _ _))
    hB.le (by positivity : 0 < R/4) hsmall hbound t ht
  rw [mem_closedBall, dist_eq_norm] at hx ⊢
  have hs' : ‖γ t - γ 0‖ < R/4 := by simpa only [mem_ball, dist_eq_norm] using hs
  calc
    ‖γ t-z‖ ≤ ‖γ t-γ 0‖ + ‖γ 0-z‖ := norm_sub_le_norm_sub_add_norm_sub _ _ _
    _ ≤ R/2 := by linarith

/-- Uniform original-domain control balls stay inside the half buffer. -/
theorem exists_compact_controlBall_buffer {m n : ℕ}
    {Ω : Set (Fin n → ℝ)} (w : Fin m → ℕ+)
    (Z : Fin m → (Fin n → ℝ) → (Fin n → ℝ))
    {z : Fin n → ℝ} {R : ℝ} (hR : 0 < R)
    (hZ : ∀ i, ContinuousOn (Z i) (closedBall z R)) :
    ∃ η : ℝ, 0 < η ∧ ∀ x ∈ closedBall z (R/4),
      {y | controlDistance Ω w Z x y < ENNReal.ofReal η} ⊆ closedBall z (R/2) := by
  obtain ⟨η, hη, _hη1, hstay⟩ := exists_compact_quarter_curve_buffer
    (Ω := Ω) w Z hR hZ
  refine ⟨η, hη, ?_⟩
  intro x hx y hy
  obtain ⟨δ, _hδ, hδη, γ, hγ, hzero, hone⟩ :=
    G1.exists_controlledCurve_of_controlDistance_lt hy
  have hh := hstay δ hδη γ hγ (by simpa only [hzero] using hx) (by norm_num : (1 : ℝ) ∈ Icc 0 1)
  simpa only [hone] using hh
end RothschildStein.G4

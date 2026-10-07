-- Copyright (c) 2026 Scott Armstrong and Amélie Loher. All rights reserved.
-- Released under Apache 2.0 license as described in the file LICENSE.
module

public import RothschildStein.G4.LinearPaths
public import Mathlib.Topology.Connected.Clopen

@[expose] public section
set_option autoImplicit false
set_option relaxedAutoImplicit false
noncomputable section
open Set Metric Filter
open scoped BigOperators Topology ENNReal

namespace RothschildStein.G4

/-- Every desired small positive auxiliary cost contains a Euclidean
neighborhood at a point where the finite controlled fields span
(BB Proposition 9.7, p. 403). -/
theorem exists_euclidean_ball_controlDistance_le {m n s : ℕ}
    {Ω : Set (Fin n → ℝ)} (hΩ : IsOpen Ω)
    {Z : Fin m → (Fin n → ℝ) → (Fin n → ℝ)}
    (hZ : ∀ j, ContDiffOn ℝ (⊤ : ℕ∞) (Z j) Ω)
    (w : Fin m → ℕ+) (hw : ∀ j, (w j : ℕ) ≤ s)
    {x₀ : Fin n → ℝ} (hx₀ : x₀ ∈ Ω)
    (hspan : ∃ B : Fin n → Fin m, frameDet Z B x₀ ≠ 0)
    {r : ℝ} (hr : 0 < r) (hr1 : r ≤ 1) :
    ∃ ε : ℝ, 0 < ε ∧ ball x₀ ε ⊆ Ω ∧
      ∀ y ∈ ball x₀ ε, controlDistance Ω w Z x₀ y ≤ ENNReal.ofReal r := by
  obtain ⟨B, R, hR, C, hC, hRΩ, hB, hbound⟩ := exists_local_frame_bound hΩ hZ hx₀ hspan
  let ε := min R (r ^ s / C) / 2
  have hmin : 0 < min R (r ^ s / C) := lt_min hR (div_pos (pow_pos hr _) hC)
  have hε : 0 < ε := half_pos hmin
  have hεR : ε < R := (half_lt_self hmin).trans_le (min_le_left _ _)
  have hεr : ε < r ^ s / C := (half_lt_self hmin).trans_le (min_le_right _ _)
  have hεK : ball x₀ ε ⊆ closedBall x₀ R :=
    ball_subset_closedBall.trans (closedBall_subset_closedBall hεR.le)
  refine ⟨ε, hε, hεK.trans hRΩ, ?_⟩
  intro y hy
  apply controlDistance_lineMap_le hZ w hw B (convex_closedBall x₀ R) hRΩ hB hbound
    (mem_closedBall_self hR.le) (hεK hy) hr hr1
  have hnε : ‖y - x₀‖ < ε := by simpa only [mem_ball, dist_eq_norm] using hy
  have hn : ‖y - x₀‖ < r ^ s / C := hnε.trans hεr
  have hm := (lt_div_iff₀ hC).mp hn
  nlinarith

end RothschildStein.G4

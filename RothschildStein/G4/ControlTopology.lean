-- Copyright (c) 2026 Scott Armstrong and Amélie Loher. All rights reserved.
-- Released under Apache 2.0 license as described in the file LICENSE.
module

public import RothschildStein.G4.LocalAuxiliary
public import RothschildStein.G4.FirstExit

@[expose] public section
set_option autoImplicit false
set_option relaxedAutoImplicit false
noncomputable section
open Set Metric Filter
open scoped BigOperators Topology ENNReal

namespace RothschildStein.G4

/-- A positive-radius ball for the original-domain control distance. -/
def controlBall {m n : ℕ} (Ω : Set (Fin n → ℝ)) (w : Fin m → ℕ+)
    (Z : Fin m → (Fin n → ℝ) → (Fin n → ℝ)) (x : Fin n → ℝ) (r : ℝ) : Set (Fin n → ℝ) :=
  {y | controlDistance Ω w Z x y < ENNReal.ofReal r}

/-- Finite control balls stay inside the original domain
(BB Definitions 9.3–9.4, p. 402). -/
theorem controlBall_subset_domain {m n : ℕ} (Ω : Set (Fin n → ℝ)) (w : Fin m → ℕ+)
    (Z : Fin m → (Fin n → ℝ) → (Fin n → ℝ)) (x : Fin n → ℝ) (r : ℝ) :
    controlBall Ω w Z x r ⊆ Ω := by
  intro y hy
  obtain ⟨δ, hδ, hδr, γ, hγ, hzero, hone⟩ := G1.exists_controlledCurve_of_controlDistance_lt hy
  rw [← hone]
  exact hγ.2.2.1 (by norm_num)

/-- First exit makes small control balls Euclidean-small using only
local field bounds; no spanning assumption is required
(BB Proposition 9.7, p. 403). -/
theorem exists_controlBall_subset_ball {m n : ℕ} {Ω : Set (Fin n → ℝ)}
    (hΩ : IsOpen Ω) {Z : Fin m → (Fin n → ℝ) → (Fin n → ℝ)}
    (hZ : ∀ j, ContinuousOn (Z j) Ω) (w : Fin m → ℕ+)
    {x : Fin n → ℝ} (hx : x ∈ Ω) {ε : ℝ} (hε : 0 < ε) :
    ∃ r : ℝ, 0 < r ∧ controlBall Ω w Z x r ⊆ ball x ε := by
  obtain ⟨d, hd, hdΩ⟩ := Metric.mem_nhds_iff.mp (hΩ.mem_nhds hx)
  let R := min ε (d / 2)
  have hR : 0 < R := lt_min hε (half_pos hd)
  have hRd : R < d := (min_le_right _ _).trans_lt (half_lt_self hd)
  have hRΩ : closedBall x R ⊆ Ω := (closedBall_subset_ball hRd).trans hdΩ
  have hc : ContinuousOn (fun z => ∑ j, ‖Z j z‖) (closedBall x R) :=
    continuousOn_finsetSum Finset.univ (fun j _ => (hZ j).norm.mono hRΩ)
  obtain ⟨M, hM⟩ := ((isCompact_closedBall x R).image_of_continuousOn hc).isBounded.exists_norm_le
  let C := |M| + 1
  have hC : 0 < C := by dsimp [C]; positivity
  have hbound : ∀ z, ‖z - x‖ ≤ R → ∑ j, ‖Z j z‖ ≤ C := by
    intro z hz
    have hzK : z ∈ closedBall x R := by simpa only [mem_closedBall, dist_eq_norm] using hz
    have hm := hM _ (mem_image_of_mem _ hzK)
    have hm' : (∑ j, ‖Z j z‖) ≤ M := (le_abs_self _).trans (by simpa only [Real.norm_eq_abs] using hm)
    exact hm'.trans ((le_abs_self M).trans (by dsimp [C]; linarith))
  let r := min 1 (R / C) / 2
  have hmin : 0 < min 1 (R / C) := lt_min zero_lt_one (div_pos hR hC)
  have hr : 0 < r := half_pos hmin
  have hr1 : r < 1 := (half_lt_self hmin).trans_le (min_le_left _ _)
  have hrR : r * C < R := (lt_div_iff₀ hC).mp
    ((half_lt_self hmin).trans_le (min_le_right _ _))
  refine ⟨r, hr, ?_⟩
  intro y hy
  obtain ⟨δ, hδ, hδr, γ, hγ, hzero, hone⟩ := G1.exists_controlledCurve_of_controlDistance_lt hy
  have hsmall : δ * C < R := (mul_lt_mul_of_pos_right hδr hC).trans hrR
  have hstay := controlledCurve_stays_ball hγ (hδr.trans hr1).le hC.le hR hsmall
    (by simpa only [hzero] using hbound) 1 (by norm_num)
  exact (ball_subset_ball (min_le_left ε (d / 2))) (by simpa only [hzero, hone] using hstay)

/-- At a spanning point, each control ball is a Euclidean
neighborhood (BB Proposition 9.7, p. 403). -/
theorem controlBall_mem_nhds_of_spanning {m n s : ℕ} {Ω : Set (Fin n → ℝ)}
    (hΩ : IsOpen Ω) {Z : Fin m → (Fin n → ℝ) → (Fin n → ℝ)}
    (hZ : ∀ j, ContDiffOn ℝ (⊤ : ℕ∞) (Z j) Ω) (w : Fin m → ℕ+)
    (hw : ∀ j, (w j : ℕ) ≤ s) {x : Fin n → ℝ} (hx : x ∈ Ω)
    (hspan : ∃ B : Fin n → Fin m, frameDet Z B x ≠ 0) {r : ℝ} (hr : 0 < r) :
    controlBall Ω w Z x r ∈ 𝓝 x := by
  let r' := min r 1 / 2
  have hmin : 0 < min r 1 := lt_min hr zero_lt_one
  have hr' : 0 < r' := half_pos hmin
  have hr'r : r' < r := (half_lt_self hmin).trans_le (min_le_left _ _)
  obtain ⟨ε, hε, hεΩ, hcost⟩ := exists_euclidean_ball_controlDistance_le hΩ hZ w hw hx hspan
    hr' ((half_lt_self hmin).trans_le (min_le_right _ _)).le
  apply mem_of_superset (ball_mem_nhds x hε)
  intro y hy
  exact (hcost y hy).trans_lt ((ENNReal.ofReal_lt_ofReal_iff hr).mpr hr'r)

end RothschildStein.G4

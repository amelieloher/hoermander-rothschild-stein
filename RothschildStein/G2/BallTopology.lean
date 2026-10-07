-- Copyright (c) 2026 Scott Armstrong and Amélie Loher. All rights reserved.
-- Released under Apache 2.0 license as described in the file LICENSE.
module

public import RothschildStein.G2.EuclideanComparison

set_option autoImplicit false
set_option relaxedAutoImplicit false
@[expose] public section
noncomputable section
open Set
namespace RothschildStein.G2
variable {N : ℕ} {G : HomogeneousGroup N}

/-- Gauge balls form a neighborhood base in the Euclidean topology
at every center (BB Thm 3.20, p. 105; translated proof). -/
theorem gaugeBall_basis {ν : (Fin N → ℝ) → ℝ} (hν : G.IsHomogeneousGauge ν)
    {U : Set (Fin N → ℝ)} (hU : IsOpen U) {x : Fin N → ℝ} (hx : x ∈ U) :
    ∃ r : ℝ, 0 < r ∧ gaugeBall G ν x r ⊆ U := by
  let e := gaugeLeftTranslation G x
  have hV : IsOpen (e ⁻¹' U) := hU.preimage e.continuous
  have hx0 : (0 : Fin N → ℝ) ∈ e ⁻¹' U := by
    change G.mul x 0 ∈ U
    have he : G.mul x 0 = x := G.zero_right x
    rwa [he]
  obtain ⟨ε, hε, hεV⟩ := Metric.mem_nhds_iff.mp (hV.mem_nhds hx0)
  obtain ⟨a, _, ha, _, hb⟩ := gauge_sublevel_norm_comparison hν 1
  refine ⟨min 1 (a * ε), lt_min zero_lt_one (mul_pos ha hε), ?_⟩
  intro y hy
  have hνu : ν (e.symm y) < min 1 (a * ε) := hy
  have hnorm : a * ‖e.symm y‖ ≤ ν (e.symm y) := (hb _ (hνu.le.trans (min_le_left _ _))).1
  have hu : e.symm y ∈ Metric.ball 0 ε := by
    rw [Metric.mem_ball, dist_zero_right]
    nlinarith [hνu.trans_le (min_le_right 1 (a * ε))]
  have hm := hεV hu
  change e (e.symm y) ∈ U at hm
  rwa [e.apply_symm_apply] at hm

/-- Gauge-ball openness characterizes exactly Euclidean openness
(BB Thm 3.20, p. 105). -/
theorem isOpen_iff_gaugeBall {ν : (Fin N → ℝ) → ℝ} (hν : G.IsHomogeneousGauge ν)
    (U : Set (Fin N → ℝ)) :
    IsOpen U ↔ ∀ x ∈ U, ∃ r : ℝ, 0 < r ∧ gaugeBall G ν x r ⊆ U := by
  constructor
  · intro h x hx
    exact gaugeBall_basis hν h hx
  · intro h
    apply isOpen_iff_mem_nhds.mpr
    intro x hx
    obtain ⟨r, hr, hb⟩ := h x hx
    exact Filter.mem_of_superset ((isOpen_gaugeBall G hν x r).mem_nhds
      (center_mem_gaugeBall G hν x hr)) hb

end RothschildStein.G2

-- Copyright (c) 2026 Scott Armstrong and Amélie Loher. All rights reserved.
-- Released under Apache 2.0 license as described in the file LICENSE.
module

public import RothschildStein.L1.FreeCanonicalCharts
public import RothschildStein.L1.CanonicalChartIdentities
public import RothschildStein.L1.CanonicalBracketAssembly
public import RothschildStein.L1.CanonicalSmoothLocalCharts
public import RothschildStein.L1.CanonicalChartSmallPatch
public import RothschildStein.L1.CanonicalExponential
public import RothschildStein.L1.CanonicalChartData
public import RothschildStein.G2.MaxGauge

@[expose] public section
set_option autoImplicit false
set_option relaxedAutoImplicit false
noncomputable section
open Set Metric Filter
open scoped Topology

namespace RothschildStein.L1.CanonicalFrameChartData

/-- Actual canonical gauges are uniformly small on a smaller
spatial patch. The coefficient patch is kept fixed (BB p. 516). -/
theorem exists_small_gauge_patch {N : ℕ} {Ω : Set (Fin N → ℝ)}
    {Y : Fin N → (Fin N → ℝ) → (Fin N → ℝ)} {x : Fin N → ℝ}
    (C : CanonicalFrameChartData Ω Y x) (G : HomogeneousGroup N)
    {δ : ℝ} (hδ : 0 < δ) :
    ∃ r : ℝ, 0 < r ∧ r ≤ C.radius ∧
      ∀ η ∈ ball x r, ∀ ξ ∈ ball x r,
        rsGauge G.weight G.weight_pos (C.theta (η, ξ)) < δ := by
  have hx : x ∈ ball x C.radius := mem_ball_self C.radius_pos
  have hc : ContinuousAt C.theta (x, x) :=
    (C.theta_smooth.contDiffAt (C.inverseDomain_open.mem_nhds
      (C.basePatch_subset ⟨hx, hx⟩))).continuousAt
  have hg := (G2.continuous_gauge G).continuousAt.comp hc
  have hm : {q | rsGauge G.weight G.weight_pos (C.theta q) < δ} ∈ 𝓝 (x, x) :=
    hg.preimage_mem_nhds (isOpen_Iio.mem_nhds (by
      change rsGauge G.weight G.weight_pos (C.theta (x, x)) < δ
      rw [C.theta_diagonal x hx, (G2.gauge_eq_zero_iff G 0).mpr rfl]
      exact hδ))
  obtain ⟨ε, hε, hsub⟩ := Metric.mem_nhds_iff.mp hm
  refine ⟨min ε C.radius, lt_min hε C.radius_pos, min_le_right _ _, ?_⟩
  intro η hη ξ hξ
  apply hsub
  rw [mem_ball, Prod.dist_eq, max_lt_iff]
  exact ⟨ball_subset_ball (min_le_left _ _) hη,
    ball_subset_ball (min_le_left _ _) hξ⟩

end RothschildStein.L1.CanonicalFrameChartData

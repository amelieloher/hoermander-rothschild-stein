-- Copyright (c) 2026 Scott Armstrong and Amélie Loher. All rights reserved.
-- Released under Apache 2.0 license as described in the file LICENSE.
module

public import RothschildStein.H3.ControlMetric
public import RothschildStein.G2.PolynomialComparison
public import RothschildStein.H2.HolderEstimates
public import Mathlib.Analysis.Calculus.ContDiff.RCLike

set_option autoImplicit false
set_option relaxedAutoImplicit false
set_option backward.isDefEq.respectTransparency false
@[expose] public section
noncomputable section
namespace RothschildStein.H3
open Set Metric MeasureTheory
open scoped NNReal ENNReal
variable {N : ℕ} (G : HomogeneousGroup N)

/-- Compact C1 sources are Lipschitz on every bounded control-gauge ball. -/
theorem compact_source_lipschitzOn_control_ball (ν : G2.HomogeneousNorm G)
    (h1 : ν.c = 1) (hsym : ν.Symmetric) (R : ℝ)
    (u : ControlCarrier N → ℝ) (hu : ContDiff ℝ 1 (fun x : Fin N → ℝ => u x))
    (hs : HasCompactSupport u) :
    let _metric := gaugeMetric G ν h1 hsym
    ∃ L : ℝ≥0, LipschitzOnWith L u (ball (0 : ControlCarrier N) R) := by
  let _metric := gaugeMetric G ν h1 hsym
  obtain ⟨L, hL⟩ := ContDiff.lipschitzWith_of_hasCompactSupport hs hu (by norm_num)
  obtain ⟨M, hM⟩ := (G2.isCompact_gauge_le ν.gauge R).bddAbove_image continuous_norm.continuousOn
  obtain ⟨a, b, ha, _, hcompare⟩ := G2.gaugeDistance_norm_comparison G ν.gauge M
  refine ⟨Real.toNNReal ((L : ℝ) * a), LipschitzOnWith.of_dist_le_mul ?_⟩
  intro x hx y hy
  have hxν : ν x ≤ R := by
    change ν (G.mul (G.inv 0) x) < R at hx
    rw [G2.inv_zero, G2.zero_mul] at hx
    exact hx.le
  have hyν : ν y ≤ R := by
    change ν (G.mul (G.inv 0) y) < R at hy
    rw [G2.inv_zero, G2.zero_mul] at hy
    exact hy.le
  have hxy := (hcompare x y (hM ⟨x, hxν, rfl⟩) (hM ⟨y, hyν, rfl⟩)).1
  have huxy := hL.dist_le_mul (x : Fin N → ℝ) y
  change dist (u x) (u y) ≤ (Real.toNNReal ((L : ℝ) * a) : ℝ) * G2.gaugeDistance G ν x y
  rw [Real.coe_toNNReal _ (mul_nonneg L.coe_nonneg ha.le)]
  calc
    _ ≤ (L : ℝ) * ‖fun i : Fin N => x i - y i‖ := by
      simpa only [dist_eq_norm, Pi.sub_def] using huxy
    _ ≤ (L : ℝ) * (a * G2.gaugeDistance G ν x y) :=
      mul_le_mul_of_nonneg_left hxy L.coe_nonneg
    _ = _ := (mul_assoc _ _ _).symm

/-- Compact C1 sources belong to every allowed local H2 Holder domain. -/
theorem compact_source_boundedHolder_control_ball (ν : G2.HomogeneousNorm G)
    (h1 : ν.c = 1) (hsym : ν.Symmetric) (R : ℝ)
    (u : ControlCarrier N → ℝ) (hu : ContDiff ℝ 1 (fun x : Fin N → ℝ => u x))
    (hs : HasCompactSupport u) {δ : ℝ≥0} (hδ : δ ≤ 1) :
    let _metric := gaugeMetric G ν h1 hsym
    H2.BoundedHolder δ (ball (0 : ControlCarrier N) R) u := by
  let _metric := gaugeMetric G ν h1 hsym
  obtain ⟨L, hL⟩ := compact_source_lipschitzOn_control_ball G ν h1 hsym R u hu hs
  obtain ⟨B, hB⟩ := hs.exists_bound_of_continuous hu.continuous
  have hsup : H2.holderSup (ball (0 : ControlCarrier N) R) u < ∞ :=
    (H2.holderSup_le_of_bound (fun x _ => by simpa only [Real.norm_eq_abs] using hB x)).trans_lt
      ENNReal.ofReal_lt_top
  have hh : HolderWith L 1 (fun x : ball (0 : ControlCarrier N) R => u x) :=
    hL.holderOnWith.holderWith
  have hsemi : H2.holderSemi 1 (ball (0 : ControlCarrier N) R) u < ∞ :=
    hh.eHolderNorm_le.trans_lt ENNReal.coe_lt_top
  have hδsemi := H2.holderSemi_le_diam (isBounded_ball) hδ hsemi
  exact ENNReal.add_lt_top.mpr ⟨hsup, hδsemi.trans_lt
    (ENNReal.mul_lt_top ENNReal.ofReal_lt_top hsemi)⟩

end RothschildStein.H3

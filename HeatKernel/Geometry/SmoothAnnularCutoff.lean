-- Copyright (c) 2026 Scott Armstrong and Amélie Loher. All rights reserved.
-- Released under Apache 2.0 license as described in the file LICENSE.
module

public import HeatKernel.Geometry.RegularizationPlateau
public import HeatKernel.Geometry.InteriorRegularizationSupport
public import HeatKernel.Geometry.SmoothLipschitzGradient
public import HeatKernel.Geometry.CoordinateBall

/-! Smooth annular cutoffs with the sharp arbitrary-gap horizontal gradient bound. -/

@[expose] public section
set_option autoImplicit false
set_option relaxedAutoImplicit false
noncomputable section
open Set MeasureTheory RothschildStein Filter
open scoped Topology NNReal ENNReal
namespace HeatKernel

/-- A strict metric annulus has a smooth compact cutoff with exact inner plateau,
values in the unit interval, and horizontal gradient bounded by two divided by the gap. -/
theorem CarnotPoint.exists_smooth_annular_cutoff {N q : ℕ} (G : HomogeneousGroup N)
    (hq : q ≤ N) (hqpos : 0 < q) (hspan : bracketSpansOn univ (G.horizontalFields hq))
    (hw : ∀ i : Fin q, G.weight (Fin.castLE hq i) = 1)
    {ν : G2.HomogeneousNorm G} (φ : G2.GroupMollifier G ν)
    (x : CarnotPoint G hq hqpos hspan) {r R : ℝ} (hrR : r < R) :
    ∃ χ : (Fin N → ℝ) → ℝ, ContDiff ℝ (⊤ : ℕ∞) χ ∧ HasCompactSupport χ ∧
      tsupport χ ⊆ (coordinateBall G hq hqpos hspan x R : Set (Fin N → ℝ)) ∧
      (∀ z, χ z ∈ Icc 0 1) ∧
      (∀ z ∈ Metric.closedBall x r, χ z = 1) ∧
      ∀ z, horizontalGradientNorm (G.horizontalFields hq) χ z ≤ 2 / (R-r) := by
  let a : ℝ := r + (R-r)/4
  let b : ℝ := a + (R-r)
  have hab : a < b := by dsimp [b]; linarith
  have hra : r < a := by dsimp [a]; linarith
  have hmid : (a+b)/2 < R := by dsimp [a,b]; linarith
  let f : CarnotPoint G hq hqpos hspan → ℝ := annularCutoff x a b
  obtain ⟨hl, hc, _, hv, hp⟩ := annularCutoff_spec G hq hqpos hspan hw x hab
  have hcont : Continuous (show (Fin N → ℝ) → ℝ from f) := hl.continuous
  have hs : tsupport (show (Fin N → ℝ) → ℝ from f) ⊆
      (coordinateBall G hq hqpos hspan x R : Set (Fin N → ℝ)) := by
    intro z hz
    have hd := tsupport_annularCutoff_subset x hab hz
    change z ∈ Metric.ball x R
    exact hd.trans_lt hmid
  let K : Set (Fin N → ℝ) := @Metric.closedBall (CarnotPoint G hq hqpos hspan) _ x r
  have hK : IsCompact K := by
    let _ : ProperSpace (CarnotPoint G hq hqpos hspan) := properSpace G hq hqpos hspan hw
    exact isCompact_closedBall x r
  have hKV : K ⊆ (coordinateBall G hq hqpos hspan x a : Set (Fin N → ℝ)) := by
    intro z hz
    change z ∈ Metric.ball x a
    exact hz.trans_lt hra
  have heq : EqOn (show (Fin N → ℝ) → ℝ from f) (fun _ => 1)
      (coordinateBall G hq hqpos hspan x a : Set (Fin N → ℝ)) := by
    intro z hz
    exact hp z (Metric.ball_subset_closedBall hz)
  have hsmooth := eventually_tsupport_groupRegularize_subset G φ hc
    (coordinateBall G hq hqpos hspan x R).isOpen hs
  have hplateau := eventually_groupRegularize_eqOn_const G φ hK
    (coordinateBall G hq hqpos hspan x a).isOpen hKV heq
  obtain ⟨ε, hεsupport, hεplateau, hεpos⟩ :=
    (hsmooth.and (hplateau.and self_mem_nhdsWithin)).exists
  change 0 < ε at hεpos
  obtain ⟨hsm, hcomp, _⟩ := groupRegularize_compact_form G hq hqpos hspan φ hεpos hl hc
  refine ⟨G2.groupRegularize G φ f ε, hsm, hcomp, hεsupport,
    groupRegularize_mem_Icc_zero_one G φ hcont hv hεpos, hεplateau, ?_⟩
  intro z
  have hg := horizontalGradientNorm_groupRegularize_le G hq hqpos hspan φ hεpos hl z
  have hgap : b-a = R-r := by dsimp [b]; ring
  simpa only [hgap, Real.coe_toNNReal _ (by positivity : 0 ≤ 2 / (R-r))] using hg

end HeatKernel

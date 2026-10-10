-- Copyright (c) 2026 Scott Armstrong and Amélie Loher. All rights reserved.
-- Released under Apache 2.0 license as described in the file LICENSE.
module

public import HeatKernel.Moser.MeanValueCutoffRadii
public import HeatKernel.Geometry.SmoothAnnularCutoff
public import RothschildStein.G2.MollifierExistence
public import HeatKernel.Moser.MeanValueSmoothSpatialWeights
import Mathlib.Analysis.Calculus.FDeriv.Congr
import Mathlib.Tactic

/-! # Two nested spatial cutoffs for positive-power testing -/

@[expose] public section
set_option autoImplicit false
set_option relaxedAutoImplicit false
noncomputable section
open Set MeasureTheory RothschildStein
open scoped Topology
namespace HeatKernel
set_option backward.isDefEq.respectTransparency false

/-- A strict annulus supplies a localization cutoff and a smaller power-test
cutoff. The first is identically one with zero horizontal derivative on the
support of the second, whose squared gradient has the explicit gap bound. -/
theorem exists_nested_smooth_power_cutoffs {N q : ℕ} (G : HomogeneousGroup N)
    (hq : q ≤ N) (hqpos : 0 < q) (hspan : bracketSpansOn univ (G.horizontalFields hq))
    (hw : ∀ i : Fin q, G.weight (Fin.castLE hq i) = 1)
    (x : CarnotPoint G hq hqpos hspan) {r R : ℝ} (hrR : r < R) :
    ∃ φ η : (Fin N → ℝ) → ℝ,
      ContDiff ℝ (⊤ : ℕ∞) φ ∧ HasCompactSupport φ ∧
      tsupport φ ⊆ (CarnotPoint.coordinateBall G hq hqpos hspan x R : Set (Fin N → ℝ)) ∧
      (∀ y, φ y ∈ Icc (0 : ℝ) 1) ∧
      ContDiff ℝ (⊤ : ℕ∞) η ∧ HasCompactSupport η ∧
      tsupport η ⊆ (CarnotPoint.coordinateBall G hq hqpos hspan x R : Set (Fin N → ℝ)) ∧
      (∀ y, η y ∈ Icc (0 : ℝ) 1) ∧
      (∀ y ∈ Metric.closedBall x r, η y = 1) ∧
      (∀ y ∈ tsupport η, φ y = 1 ∧
        ∀ i, fieldDerivative (G.horizontalFields hq i) φ y = 0) ∧
      ∀ y, (∑ i, fieldDerivative (G.horizontalFields hq i) η y ^ 2) ≤ 16 / (R - r) ^ 2 := by
  let ψ := Classical.choice (G2.nonempty_groupMollifier (G := G) (G2.smoothNorm G))
  let mid := (r + R) / 2
  have hrmid : r < mid := by dsimp only [mid]; linarith
  have hmidR : mid < R := by dsimp only [mid]; linarith
  obtain ⟨φ, hφ, hcφ, hsφ, hφunit, hφone, _⟩ :=
    CarnotPoint.exists_smooth_annular_cutoff G hq hqpos hspan hw ψ x hmidR
  obtain ⟨η, hη, hcη, hsη, hηunit, hηone, hηgrad⟩ :=
    CarnotPoint.exists_smooth_annular_cutoff G hq hqpos hspan hw ψ x hrmid
  refine ⟨φ, η, hφ, hcφ, hsφ, hφunit, hη, hcη,
    hsη.trans (Metric.ball_subset_ball (α := CarnotPoint G hq hqpos hspan) hmidR.le),
    hηunit, hηone, ?_, ?_⟩
  · intro y hy
    have hymid := hsη hy
    have he : φ =ᶠ[𝓝 y] fun _ => 1 := by
      filter_upwards [(CarnotPoint.coordinateBall G hq hqpos hspan x mid).isOpen.mem_nhds hymid]
        with z hz
      exact hφone z (Metric.ball_subset_closedBall hz)
    refine ⟨he.eq_of_nhds, fun i => ?_⟩
    unfold fieldDerivative
    rw [he.fderiv_eq]
    simp
  · intro y
    have hnonneg : 0 ≤ ∑ i, (fderiv ℝ η y (G.horizontalFields hq i y)) ^ 2 :=
      Finset.sum_nonneg fun _ _ => sq_nonneg _
    have hs := pow_le_pow_left₀ (Real.sqrt_nonneg _) (hηgrad y) 2
    have heq : (2 / (mid - r)) ^ 2 = 16 / (R - r) ^ 2 := by
      dsimp only [mid]
      field_simp
      ring
    simpa only [horizontalGradientNorm, Real.sq_sqrt hnonneg, fieldDerivative, heq] using hs

end HeatKernel

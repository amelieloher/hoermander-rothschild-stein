-- Copyright (c) 2026 Scott Armstrong and Amélie Loher. All rights reserved.
-- Released under Apache 2.0 license as described in the file LICENSE.
module

public import HeatKernel.Geometry.CarnotPoint
public import Mathlib.Topology.MetricSpace.Lipschitz

/-! Compactly supported metric cutoffs with the exact arbitrary-annulus Lipschitz bound. -/

@[expose] public section
set_option autoImplicit false
set_option relaxedAutoImplicit false
noncomputable section
open Set
namespace HeatKernel

/-- A metric annulus cutoff whose support ends at the midpoint of the two radii. -/
def annularCutoff {A : Type*} [PseudoMetricSpace A] (x : A) (r R : ℝ) (z : A) : ℝ :=
  min 1 (max 0 (((r + R) / 2 - dist x z) * (2 / (R - r))))

/-- An annular cutoff takes values in the unit interval. -/
theorem annularCutoff_mem_Icc {A : Type*} [PseudoMetricSpace A]
    (x : A) (r R : ℝ) (z : A) : annularCutoff x r R z ∈ Icc 0 1 :=
  ⟨le_min (by norm_num) (le_max_left _ _), min_le_left _ _⟩

/-- The plateau includes the entire closed inner ball. -/
theorem annularCutoff_eq_one {A : Type*} [PseudoMetricSpace A]
    (x : A) {r R : ℝ} (hrR : r < R) {z : A} (hz : dist x z ≤ r) :
    annularCutoff x r R z = 1 := by
  have hk : 0 < 2 / (R - r) := div_pos (by norm_num) (sub_pos.mpr hrR)
  have he : ((r + R) / 2 - r) * (2 / (R - r)) = 1 := by
    field_simp [ne_of_gt (sub_pos.mpr hrR)]
    ring
  apply min_eq_left
  apply le_trans _ (le_max_right _ _)
  rw [← he]
  exact mul_le_mul_of_nonneg_right (by linarith) hk.le

/-- An annular cutoff vanishes outside its midpoint radius. -/
theorem annularCutoff_eq_zero {A : Type*} [PseudoMetricSpace A]
    (x : A) {r R : ℝ} (hrR : r < R) {z : A} (hz : (r + R) / 2 ≤ dist x z) :
    annularCutoff x r R z = 0 := by
  have hk : 0 ≤ 2 / (R - r) := (div_pos (by norm_num) (sub_pos.mpr hrR)).le
  simp only [annularCutoff, max_eq_left (mul_nonpos_of_nonpos_of_nonneg (sub_nonpos.mpr hz) hk)]
  norm_num

/-- The Lipschitz constant of the arbitrary-annulus cutoff is exactly two divided by the gap. -/
theorem lipschitzWith_annularCutoff {A : Type*} [PseudoMetricSpace A]
    (x : A) {r R : ℝ} (hrR : r < R) :
    LipschitzWith (Real.toNNReal (2 / (R - r))) (annularCutoff x r R) := by
  have hk : 0 < 2 / (R - r) := div_pos (by norm_num) (sub_pos.mpr hrR)
  have ha : LipschitzWith (Real.toNNReal (2 / (R - r)))
      (fun s : ℝ => ((r + R) / 2 - s) * (2 / (R - r))) := by
    apply LipschitzWith.of_dist_le_mul
    intro s t
    have he : ((r + R) / 2 - s) * (2 / (R - r)) -
        ((r + R) / 2 - t) * (2 / (R - r)) = (t - s) * (2 / (R - r)) := by ring
    rw [Real.dist_eq, he, abs_mul, abs_of_pos hk, Real.dist_eq, abs_sub_comm,
      Real.coe_toNNReal _ hk.le]
    exact le_of_eq (_root_.mul_comm _ _)
  change LipschitzWith _ (fun z => min 1 (max 0 (((r + R) / 2 - dist x z) * (2 / (R - r)))))
  simpa only [Function.comp_def, mul_one] using
    ((ha.const_max 0).const_min 1).comp (LipschitzWith.dist_right x)

/-- The topological support lies in the closed midpoint ball. -/
theorem tsupport_annularCutoff_subset {A : Type*} [PseudoMetricSpace A]
    (x : A) {r R : ℝ} (hrR : r < R) :
    tsupport (annularCutoff x r R) ⊆ Metric.closedBall x ((r + R) / 2) := by
  apply closure_minimal _ Metric.isClosed_closedBall
  intro z hz
  rw [Metric.mem_closedBall, dist_comm]
  by_contra h
  exact hz (annularCutoff_eq_zero x hrR (le_of_lt (lt_of_not_ge h)))

/-- In a proper space the annular cutoff has compact support strictly inside the outer ball. -/
theorem annularCutoff_compact_support {A : Type*} [PseudoMetricSpace A] [ProperSpace A]
    (x : A) {r R : ℝ} (hrR : r < R) :
    HasCompactSupport (annularCutoff x r R) ∧ tsupport (annularCutoff x r R) ⊆ Metric.ball x R := by
  have hs := tsupport_annularCutoff_subset x hrR
  refine ⟨(isCompact_closedBall x ((r + R) / 2)).of_isClosed_subset (isClosed_tsupport _) hs, ?_⟩
  intro z hz
  have hd := hs hz
  rw [Metric.mem_closedBall] at hd
  exact hd.trans_lt (by linarith)

/-- The arbitrary-annulus cutoff on a homogeneous horizontal metric space has compact
support inside the outer ball, the inner plateau, and the exact gap bound. -/
theorem CarnotPoint.annularCutoff_spec {N q : ℕ} (G : RothschildStein.HomogeneousGroup N)
    (hq : q ≤ N) (hqpos : 0 < q)
    (hspan : RothschildStein.bracketSpansOn univ (G.horizontalFields hq))
    (hw : ∀ i : Fin q, G.weight (Fin.castLE hq i) = 1)
    (x : CarnotPoint G hq hqpos hspan) {r R : ℝ} (hrR : r < R) :
    LipschitzWith (Real.toNNReal (2 / (R - r))) (annularCutoff x r R) ∧
      HasCompactSupport (annularCutoff x r R) ∧
      tsupport (annularCutoff x r R) ⊆ Metric.ball x R ∧
      (∀ z, annularCutoff x r R z ∈ Icc 0 1) ∧
      ∀ z ∈ Metric.closedBall x r, annularCutoff x r R z = 1 := by
  let _ : ProperSpace (CarnotPoint G hq hqpos hspan) := CarnotPoint.properSpace G hq hqpos hspan hw
  obtain ⟨hc, hs⟩ := annularCutoff_compact_support x hrR
  refine ⟨lipschitzWith_annularCutoff x hrR, hc, hs, annularCutoff_mem_Icc x r R, ?_⟩
  intro z hz
  exact annularCutoff_eq_one x hrR (by simpa only [Metric.mem_closedBall, dist_comm] using hz)

end HeatKernel

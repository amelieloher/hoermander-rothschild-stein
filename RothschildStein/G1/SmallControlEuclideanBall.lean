-- Copyright (c) 2026 Scott Armstrong and Amélie Loher. All rights reserved.
-- Released under Apache 2.0 license as described in the file LICENSE.
module

public import RothschildStein.G1.ControlEMetric
public import Mathlib.Analysis.Normed.Module.FiniteDimension

set_option autoImplicit false
set_option relaxedAutoImplicit false
set_option backward.isDefEq.respectTransparency false
@[expose] public section
noncomputable section
open Set Metric Filter
open scoped Topology BigOperators ENNReal
namespace RothschildStein.G1

/-- A sufficiently small control ball lies in a prescribed
Euclidean ball by the first-exit estimate, for arbitrary positive weights
(BB Thm 1.53, (1.46), pp. 35–36). -/
theorem norm_sub_lt_of_controlDistance_lt_buffer {m n : ℕ}
    {Ω : Set (Fin n → ℝ)} {w : Fin m → ℕ+}
    {X : Fin m → (Fin n → ℝ) → (Fin n → ℝ)}
    {x y : Fin n → ℝ} {B R : ℝ} (hB : 0 < B) (hR : 0 < R)
    (hbound : ∀ z, ‖z - x‖ ≤ R → ∑ i, ‖X i z‖ ≤ B)
    (hd : controlDistance Ω w X x y < ENNReal.ofReal (min 1 (R/B))) :
    ‖y-x‖ < R := by
  by_contra hn
  obtain ⟨δ,hδ,hδr,γ,hγ,hγ0,hγ1⟩ := exists_controlledCurve_of_controlDistance_lt hd
  have hm := controlledCurve_firstExit_bound hγ
    (hδr.trans_le (min_le_left _ _)).le hB.le hR
    (by simpa only [hγ0,hγ1] using le_of_not_gt hn)
    (by simpa only [hγ0] using hbound)
  have hs := (lt_div_iff₀ hB).mp (hδr.trans_le (min_le_right _ _))
  linarith

/-- Every Euclidean neighborhood contains a positive-radius
control ball. This direction needs continuous fields, without bracket rank
or Chow finiteness (BB Thm 1.53, (1.46), pp. 35–36). -/
theorem exists_controlBall_subset_euclideanBall {m n : ℕ}
    {Ω : Set (Fin n → ℝ)} (hΩ : IsOpen Ω) (w : Fin m → ℕ+)
    (X : Fin m → (Fin n → ℝ) → (Fin n → ℝ))
    (hX : ∀ i, ContinuousOn (X i) Ω) {x : Fin n → ℝ} (hx : x ∈ Ω)
    {r : ℝ} (hr : 0 < r) :
    ∃ ε : ℝ, 0 < ε ∧ ∀ y,
      controlDistance Ω w X x y < ENNReal.ofReal ε → dist y x < r := by
  obtain ⟨a,ha,hball⟩ := Metric.mem_nhds_iff.mp (hΩ.mem_nhds hx)
  let R := min (a/2) r
  have hR : 0 < R := lt_min (by positivity) hr
  have hKΩ : closedBall x R ⊆ Ω := by
    intro z hz
    apply hball
    exact (show dist z x ≤ R from hz).trans_lt
      ((min_le_left _ _).trans_lt (by linarith))
  have hc : ContinuousOn (fun z => ∑ i, ‖X i z‖) (closedBall x R) :=
    continuousOn_finsetSum _ (fun i _ => ((hX i).mono hKΩ).norm)
  obtain ⟨B,hbound⟩ := ((isCompact_closedBall x R).image_of_continuousOn hc).isBounded.exists_norm_le
  have hB : 0 < max 1 B := zero_lt_one.trans_le (le_max_left _ _)
  refine ⟨min 1 (R/max 1 B),lt_min zero_lt_one (div_pos hR hB),?_⟩
  intro y hy
  have hn := norm_sub_lt_of_controlDistance_lt_buffer hB hR (x := x) (y := y)
    (Ω := Ω) (w := w) (X := X) (fun z hz => ?_) hy
  · simpa only [dist_eq_norm] using hn.trans_le (min_le_right _ _)
  · have hb := hbound _ (mem_image_of_mem _ (show z ∈ closedBall x R from by
      simpa only [mem_closedBall,dist_eq_norm] using hz))
    exact (le_abs_self _).trans (hb.trans (le_max_right _ _))

/-- Euclidean-open subsets of the domain are open for the
intrinsic extended control metric. The converse uses local control-distance comparison
(BB Thm 1.53, pp. 35–36). -/
theorem isOpen_control_of_isOpen_euclidean {m n : ℕ}
    {Ω : Set (Fin n → ℝ)} (hΩ : IsOpen Ω) (w : Fin m → ℕ+)
    (X : Fin m → (Fin n → ℝ) → (Fin n → ℝ))
    (hX : ∀ i, ContinuousOn (X i) Ω) {U : Set Ω} (hU : IsOpen U) :
    @IsOpen Ω (controlEMetricSpace hΩ w X hX).toUniformSpace.toTopologicalSpace U := by
  apply (@EMetric.isOpen_iff Ω U (controlEMetricSpace hΩ w X hX).toPseudoEMetricSpace).mpr
  intro x hx
  obtain ⟨r,hr,hsub⟩ := Metric.isOpen_iff.mp hU x hx
  obtain ⟨ε,hε,hεsub⟩ := exists_controlBall_subset_euclideanBall hΩ w X hX x.property hr
  refine ⟨ENNReal.ofReal ε,ENNReal.ofReal_pos.mpr hε,?_⟩
  intro y hy
  apply hsub
  change controlDistance Ω w X y.val x.val < ENNReal.ofReal ε at hy
  rw [controlDistance_symm Ω w X y.val x.val] at hy
  exact hεsub y.val hy

end RothschildStein.G1

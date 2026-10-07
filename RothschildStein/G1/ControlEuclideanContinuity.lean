-- Copyright (c) 2026 Scott Armstrong and Amélie Loher. All rights reserved.
-- Released under Apache 2.0 license as described in the file LICENSE.
module

public import RothschildStein.G1.ComparisonControlTopology
public import RothschildStein.G1.OpenOrbits

set_option autoImplicit false
set_option relaxedAutoImplicit false
set_option backward.isDefEq.respectTransparency false
@[expose] public section
noncomputable section
open Set Metric Filter
open scoped Topology ENNReal
namespace RothschildStein.G1

/-- The intrinsic control extended
metric with definitionally the original Euclidean subtype topology
(BB Thm 1.53, pp. 35–36). -/
@[instance_reducible]
def controlEuclideanEMetric_of_local_comparison {m n s : ℕ}
    {Ω : Set (Fin n → ℝ)} (hΩ : IsOpen Ω) (w : Fin m → ℕ+)
    (X : Fin m → (Fin n → ℝ) → (Fin n → ℝ))
    (hX : ∀ i, ContinuousOn (X i) Ω) (hs : 0 < s)
    (hcomparison : LocalControlComparison Ω w X s) : EMetricSpace Ω :=
  (controlEMetricSpace hΩ w X hX).replaceTopology
    (controlEMetricSpace_topology_eq_of_local_comparison hΩ w X hX hs hcomparison).symm

/-- Joint Euclidean continuity of
exactly the extended control distance, even before connectivity
or distance finiteness (BB Thm 1.53, pp. 35–36). -/
theorem continuous_controlDistance_of_local_comparison {m n s : ℕ}
    {Ω : Set (Fin n → ℝ)} (hΩ : IsOpen Ω) (w : Fin m → ℕ+)
    (X : Fin m → (Fin n → ℝ) → (Fin n → ℝ))
    (hX : ∀ i, ContinuousOn (X i) Ω) (hs : 0 < s)
    (hcomparison : LocalControlComparison Ω w X s) :
    Continuous (fun p : Ω × Ω => controlDistance Ω w X p.1.val p.2.val) := by
  let M := controlEuclideanEMetric_of_local_comparison hΩ w X hX hs hcomparison
  exact @continuous_edist Ω M.toPseudoEMetricSpace

/-- Local finite-distance neighborhoods
and connectedness give global Chow finiteness. The local estimate is
used without assuming the conclusion of Chow (BB Thm 1.45, p. 34). -/
theorem controlDistance_ne_top_of_local_comparison {m n s : ℕ}
    {Ω : Set (Fin n → ℝ)} (hΩ : IsOpen Ω) (hconn : IsPreconnected Ω)
    (w : Fin m → ℕ+) (X : Fin m → (Fin n → ℝ) → (Fin n → ℝ))
    (hs : 0 < s) (hcomparison : LocalControlComparison Ω w X s)
    {x y : Fin n → ℝ} (hx : x ∈ Ω) (hy : y ∈ Ω) :
    controlDistance Ω w X x y ≠ ∞ := by
  apply relation_universal_of_local_reachability hconn
    (fun a b => controlDistance Ω w X a b ≠ ∞) ?_ ?_ ?_ ?_ hx hy
  · intro z hz
    rw [controlDistance_self w X hz]
    exact ENNReal.zero_ne_top
  · intro a b hab
    rwa [controlDistance_symm Ω w X b a]
  · intro a b c hab hbc
    exact ne_top_of_le_ne_top (ENNReal.add_ne_top.mpr ⟨hab,hbc⟩)
      (controlDistance_triangle Ω w X a b c)
  · intro z hz
    obtain ⟨r,hr,hrsub⟩ := exists_euclideanBall_subset_controlBall_of_local_comparison
      hs hcomparison hz (show (0 : ℝ≥0∞) < ∞ from ENNReal.zero_lt_top)
    obtain ⟨a,ha,hasub⟩ := Metric.mem_nhds_iff.mp (hΩ.mem_nhds hz)
    refine ⟨ball z (min r a),isOpen_ball,mem_ball_self (lt_min hr ha),?_,?_⟩
    · intro v hv
      change dist v z < min r a at hv
      exact hasub (hv.trans_le (min_le_right _ _))
    · intro v hv
      change dist v z < min r a at hv
      exact (hrsub v (hasub (hv.trans_le (min_le_right _ _)))
        (hv.trans_le (min_le_left _ _))).ne

end RothschildStein.G1

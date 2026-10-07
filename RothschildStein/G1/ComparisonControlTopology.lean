-- Copyright (c) 2026 Scott Armstrong and Amélie Loher. All rights reserved.
-- Released under Apache 2.0 license as described in the file LICENSE.
module

public import RothschildStein.G1.SmallControlEuclideanBall
public import Mathlib.Analysis.SpecialFunctions.Pow.Continuity
public import Mathlib.Topology.Instances.ENNReal.Lemmas

set_option autoImplicit false
set_option relaxedAutoImplicit false
set_option backward.isDefEq.respectTransparency false
@[expose] public section
noncomputable section
open Set Filter Metric
open scoped Topology ENNReal
namespace RothschildStein.G1

/-- The full near-diagonal comparison clause on compact
patches, retaining both bounds and all three positive constants
(BB Thm 1.53, (1.45), p. 35). -/
def LocalControlComparison {m n : ℕ} (Ω : Set (Fin n → ℝ))
    (w : Fin m → ℕ+) (X : Fin m → (Fin n → ℝ) → (Fin n → ℝ)) (s : ℕ) : Prop :=
  ∀ K : Set (Fin n → ℝ), IsCompact K → K ⊆ Ω →
    ∃ ρ cminus cplus : ℝ, 0 < ρ ∧ 0 < cminus ∧ 0 < cplus ∧
      ∀ x ∈ K, ∀ y ∈ Ω, ‖y-x‖ < ρ →
        ENNReal.ofReal (cminus * ‖y-x‖) ≤ controlDistance Ω w X x y ∧
        controlDistance Ω w X x y ≤ ENNReal.ofReal (cplus * ‖y-x‖ ^ (1/(s : ℝ)))

/-- The exact compact-patch local
comparison gives a Euclidean ball inside each positive control ball
(BB Thm 1.53, (1.46), pp. 35–36). -/
theorem exists_euclideanBall_subset_controlBall_of_local_comparison {m n s : ℕ}
    {Ω : Set (Fin n → ℝ)} {w : Fin m → ℕ+}
    {X : Fin m → (Fin n → ℝ) → (Fin n → ℝ)}
    (hs : 0 < s) (hcomparison : LocalControlComparison Ω w X s)
    {x : Fin n → ℝ} (hx : x ∈ Ω) {ε : ℝ≥0∞} (hε : 0 < ε) :
    ∃ r : ℝ, 0 < r ∧ ∀ y ∈ Ω, dist y x < r → controlDistance Ω w X x y < ε := by
  obtain ⟨ρ,cminus,cplus,hρ,_,_,hcmp⟩ :=
    hcomparison {x} isCompact_singleton (singleton_subset_iff.mpr hx)
  have ha : 0 < 1/(s : ℝ) := by positivity
  let F : (Fin n → ℝ) → ℝ≥0∞ :=
    fun y => ENNReal.ofReal (cplus * ‖y-x‖ ^ (1/(s : ℝ)))
  have hF : Continuous F := ENNReal.continuous_ofReal.comp
    (continuous_const.mul ((continuous_id.sub continuous_const).norm.rpow_const (fun _ => Or.inr ha.le)))
  have hFx : F x = 0 := by
    change ENNReal.ofReal (cplus * ‖x-x‖ ^ (1/(s : ℝ))) = 0
    rw [sub_self,norm_zero,Real.zero_rpow (ne_of_gt ha),mul_zero,ENNReal.ofReal_zero]
  have hn : {y | F y < ε} ∈ 𝓝 x := hF.continuousAt.preimage_mem_nhds
    (Iio_mem_nhds (by rw [hFx]; exact hε))
  obtain ⟨r,hr,hsub⟩ := Metric.mem_nhds_iff.mp hn
  refine ⟨min r ρ,lt_min hr hρ,?_⟩
  intro y hy hyr
  have hnear : ‖y-x‖ < ρ := by
    simpa only [dist_eq_norm] using hyr.trans_le (min_le_right _ _)
  exact (hcmp x (mem_singleton x) y hy hnear).2.trans_lt
    (hsub (hyr.trans_le (min_le_left _ _)))

/-- The two ball inclusions identify
exactly the intrinsic control topology and the original Euclidean subtype
topology, before any connectedness or distance finiteness assumption
(BB Thm 1.53, pp. 35–36). -/
theorem controlEMetricSpace_topology_eq_of_local_comparison {m n s : ℕ}
    {Ω : Set (Fin n → ℝ)} (hΩ : IsOpen Ω) (w : Fin m → ℕ+)
    (X : Fin m → (Fin n → ℝ) → (Fin n → ℝ))
    (hX : ∀ i, ContinuousOn (X i) Ω) (hs : 0 < s)
    (hcomparison : LocalControlComparison Ω w X s) :
    (controlEMetricSpace hΩ w X hX).toUniformSpace.toTopologicalSpace =
      (inferInstance : TopologicalSpace Ω) := by
  apply TopologicalSpace.ext
  funext U
  apply propext
  constructor
  · intro hU
    apply Metric.isOpen_iff.mpr
    intro x hx
    obtain ⟨ε,hε,hsub⟩ :=
      (@EMetric.isOpen_iff Ω U (controlEMetricSpace hΩ w X hX).toPseudoEMetricSpace).mp hU x hx
    obtain ⟨r,hr,hrsub⟩ := exists_euclideanBall_subset_controlBall_of_local_comparison
      hs hcomparison x.property hε
    refine ⟨r,hr,?_⟩
    intro y hy
    apply hsub
    change controlDistance Ω w X y.val x.val < ε
    rw [controlDistance_symm Ω w X y.val x.val]
    exact hrsub y.val y.property hy
  · exact isOpen_control_of_isOpen_euclidean hΩ w X hX

end RothschildStein.G1

-- Copyright (c) 2026 Scott Armstrong and Amélie Loher. All rights reserved.
-- Released under Apache 2.0 license as described in the file LICENSE.
module

public import RothschildStein.P2.SmoothingTheorem
public import RothschildStein.G1.ControlEMetric
public import RothschildStein.G4.ControlTopology
public import RothschildStein.S.ControlBallPartition
public import RothschildStein.S.HolderFiniteCover

/-!
# Distributional smoothing: the finite-cover step for the Hölder case (`memHolderXLoc`)

The local Hölder statement of `smoothing_holder_of_localSolvability` gives `u ∈ C^{2,α}_X(A)` on a
neighborhood `A` of every point. `memHolderXLoc` asks for `u ∈ C^{2,α}_X(V)` for every
`V ⋐ Ω`, with the Hölder seminorm over all pairs of `V` for the control distance of `Ω`. This file
adds the finite covering argument (BB (2.23), p. 85; (11.79), p. 592; as in the finite cover of the
base Hölder estimate):

* `controlDistanceGeometry`: the extended metric `d_{X,Ω}` satisfies the hypotheses `HD1`-`HD2`
  (`S.DistanceGeometry` for the control distance of the original fields), with the topology comparison obtained from the lifted charts
  (Euclidean convergence implies `d`-convergence, `exists_controlDistance_lt_of_euclid_close`) and
  the first-exit lemma (`G4.exists_controlBall_subset_ball`);
* `holderENorm_lt_top_of_local_balls`: finite Hölder norm near every point gives finite Hölder norm
  on every `V ⋐ Ω` (Lebesgue number of the cover of the compact `closure V`, a finite net of centres,
  the finite control-ball partition of unity of BB (2.23), together with HD3).
-/

set_option autoImplicit false
set_option relaxedAutoImplicit false

@[expose] public section
noncomputable section
open Set MeasureTheory Filter TopologicalSpace Metric
open scoped ENNReal NNReal Topology BigOperators
open RothschildStein.P1
namespace RothschildStein.P2

section Geometry

variable {n q : ℕ}

/-- **HD1-HD2 for the control distance of `Ω`, from the lifted charts.** The weighted
control distance `d_{X,Ω}` is an extended metric inducing the Euclidean topology of `Ω`: control
balls are Euclidean open (`isOpen_rsBall_base`, through the charts) and every Euclidean neighborhood
of a point contains a control ball (first exit, `G4.exists_controlBall_subset_ball`). -/
def controlDistanceGeometry (Ω : Opens (Fin n → ℝ)) (X : Fin (q + 1) → (Fin n → ℝ) → (Fin n → ℝ))
    (hX : ∀ i, ContDiffOn ℝ (⊤ : ℕ∞) (X i) (Ω : Set (Fin n → ℝ)))
    (hchart : ∀ x₀ ∈ (Ω : Set (Fin n → ℝ)), ∃ (s m : ℕ),
      Nonempty (P1.LiftedChart driftWeight s (Ω : Set (Fin n → ℝ)) Ω.isOpen X x₀ m)) :
    S.DistanceGeometry Ω where
  d := controlDistance (Ω : Set (Fin n → ℝ)) driftWeight X
  metric := G1.controlEMetricSpace Ω.isOpen driftWeight X (fun i => (hX i).continuousOn)
  distance_eq := fun x y => rfl
  topology_eq := by
    let M : EMetricSpace Ω :=
      G1.controlEMetricSpace Ω.isOpen driftWeight X (fun i => (hX i).continuousOn)
    refine TopologicalSpace.ext_iff.2 fun s => ?_
    rw [@EMetric.isOpen_iff Ω s M.toPseudoEMetricSpace]
    constructor
    · intro hs x hx
      obtain ⟨U, hU, rfl⟩ := isOpen_induced_iff.1 hs
      obtain ⟨ε, hε, hball⟩ := Metric.isOpen_iff.1 hU x.1 hx
      obtain ⟨r, hr, hr'⟩ := G4.exists_controlBall_subset_ball Ω.isOpen
        (fun j => (hX j).continuousOn) driftWeight x.2 hε
      refine ⟨ENNReal.ofReal r, ENNReal.ofReal_pos.2 hr, fun y hy => ?_⟩
      have hy0 : controlDistance (Ω : Set (Fin n → ℝ)) driftWeight X y.1 x.1 <
          ENNReal.ofReal r := hy
      have hy' : controlDistance (Ω : Set (Fin n → ℝ)) driftWeight X x.1 y.1 <
          ENNReal.ofReal r := by
        rw [G1.controlDistance_symm]; exact hy0
      exact hball (hr' hy')
    · intro hs
      refine isOpen_iff_mem_nhds.2 fun x hx => ?_
      obtain ⟨ε, hε, hball⟩ := hs x hx
      have hmin : 0 < min ε 1 := lt_min hε zero_lt_one
      have hmin_ne : min ε 1 ≠ ⊤ := ne_top_of_le_ne_top ENNReal.one_ne_top (min_le_right _ _)
      have hreal : 0 < (min ε 1).toReal := ENNReal.toReal_pos hmin.ne' hmin_ne
      obtain ⟨sc, mc, ⟨C⟩⟩ := hchart x.1 x.2
      have hmem : x.1 ∈ basePoint '' C.U :=
        ⟨joinPoint x.1 (0 : Fin mc → ℝ), C.center_mem, basePoint_joinPoint x.1 0⟩
      obtain ⟨δ', hδ', hclose⟩ := exists_controlDistance_lt_of_euclid_close C hmem hreal
      have hopen : IsOpen {y : Ω | ‖y.1 - x.1‖ < δ'} :=
        isOpen_lt (continuous_norm.comp (continuous_subtype_val.sub continuous_const))
          continuous_const
      refine Filter.mem_of_superset (hopen.mem_nhds (by simpa using hδ')) fun y hy => ?_
      refine hball ?_
      have h1 := (hclose y.1 hy).2
      rw [ENNReal.ofReal_toReal hmin_ne] at h1
      have h2 : controlDistance (Ω : Set (Fin n → ℝ)) driftWeight X y.1 x.1 < ε := by
        rw [G1.controlDistance_symm]; exact h1.trans_le (min_le_left _ _)
      exact h2

theorem exists_pos_le_forall_finset {ι : Type*} (t : Finset ι) (ρ : ι → ℝ)
    (hρ : ∀ i ∈ t, 0 < ρ i) : ∃ r : ℝ, 0 < r ∧ ∀ i ∈ t, r ≤ ρ i := by
  classical
  induction t using Finset.induction_on with
  | empty => exact ⟨1, one_pos, by simp⟩
  | insert a t ha ih =>
    obtain ⟨r, hr0, hr⟩ := ih (fun i hi => hρ i (Finset.mem_insert_of_mem hi))
    have hρa := hρ a (Finset.mem_insert_self a t)
    refine ⟨min r (ρ a), lt_min hr0 hρa, fun i hi => ?_⟩
    rcases Finset.mem_insert.1 hi with rfl | hi
    · exact min_le_right _ _
    · exact (min_le_left _ _).trans (hr i hi)

/-- **Finite Hölder norm near every point gives finite Hölder norm
on every relatively compact `V ⋐ Ω`.** If `f` has finite `C^α` norm (for the control distance of `Ω`)
on a neighborhood `A` of every point of `Ω`, then it has finite `C^α` norm on every open `V` with
compact closure in `Ω`. Proof: a Lebesgue number `r` of the cover of the compact `closure V` by
small control balls (the balls of radius `ρ_y/2` around finitely many points, `r = min ρ_y/4`), a
finite net of centres at scale `r`, the finite smooth partition of unity subordinate to the
`2r`-balls (`exists_finite_control_ball_partition`, HD3 on a relatively compact patch) and the
covering inequality `holderENorm_finite_partition_cover_le` (BB (2.23), p. 85). -/
theorem holderENorm_lt_top_of_local_balls (Ω : Opens (Fin n → ℝ))
    (X : Fin (q + 1) → (Fin n → ℝ) → (Fin n → ℝ))
    (hX : ∀ i, ContDiffOn ℝ (⊤ : ℕ∞) (X i) (Ω : Set (Fin n → ℝ)))
    (hchart : ∀ x₀ ∈ (Ω : Set (Fin n → ℝ)), ∃ (s m : ℕ),
      Nonempty (P1.LiftedChart driftWeight s (Ω : Set (Fin n → ℝ)) Ω.isOpen X x₀ m))
    {α : ℝ} (hα : 0 < α) (hα1 : α ≤ 1) {V : Opens (Fin n → ℝ)}
    (hVc : IsCompact (closure (V : Set (Fin n → ℝ)))) (hVΩ : closure (V : Set (Fin n → ℝ)) ⊆ Ω)
    {f : (Fin n → ℝ) → ℝ}
    (hloc : ∀ y ∈ (Ω : Set (Fin n → ℝ)), ∃ A : Opens (Fin n → ℝ), y ∈ (A : Set (Fin n → ℝ)) ∧
      A ≤ Ω ∧ holderENorm (controlDistance (Ω : Set (Fin n → ℝ)) driftWeight X) α
        (A : Set (Fin n → ℝ)) f < ⊤) :
    holderENorm (controlDistance (Ω : Set (Fin n → ℝ)) driftWeight X) α (V : Set (Fin n → ℝ)) f <
      ⊤ := by
  classical
  let G := controlDistanceGeometry Ω X hX hchart
  have hG : G.d = controlDistance (Ω : Set (Fin n → ℝ)) driftWeight X := rfl
  have hw : ∀ i : Fin (q + 1), ((driftWeight i : ℕ+) : ℕ) ≤ 2 := driftWeight_coe_le_two
  -- radii around each point of `Ω`
  have hrad : ∀ y ∈ (Ω : Set (Fin n → ℝ)), ∃ ε ρ : ℝ, 0 < ε ∧ 0 < ρ ∧
      closedBall y ε ⊆ (Ω : Set (Fin n → ℝ)) ∧
      rsBall (Ω : Set (Fin n → ℝ)) driftWeight X y ρ ⊆ ball y ε ∧
      holderENorm (controlDistance (Ω : Set (Fin n → ℝ)) driftWeight X) α (ball y ε) f < ⊤ := by
    intro y hy
    obtain ⟨A, hyA, hAΩ, hfA⟩ := hloc y hy
    obtain ⟨e₁, he₁, hball₁⟩ := Metric.isOpen_iff.1 A.isOpen y hyA
    have hε : 0 < e₁ / 2 := half_pos he₁
    have hsubA : ball y (e₁ / 2) ⊆ A := (ball_subset_ball (by linarith)).trans hball₁
    obtain ⟨ρ, hρ, hρ'⟩ := G4.exists_controlBall_subset_ball Ω.isOpen
      (fun j => (hX j).continuousOn) driftWeight hy hε
    refine ⟨e₁ / 2, ρ, hε, hρ, (closedBall_subset_ball (by linarith)).trans
      (hball₁.trans (fun z hz => hAΩ hz)), fun z hz => hρ' hz.2, ?_⟩
    exact lt_of_le_of_lt (RothschildStein.S.holderENorm_mono
      (controlDistance (Ω : Set (Fin n → ℝ)) driftWeight X) α (A : Set (Fin n → ℝ)) f hsubA) hfA
  choose! ε ρ hε hρ hcb hrb hfin using hrad
  have hKΩ : ∀ y ∈ closure (V : Set (Fin n → ℝ)), y ∈ (Ω : Set (Fin n → ℝ)) :=
    fun _ hy => hVΩ hy
  have hKΩ' : ∀ y : closure (V : Set (Fin n → ℝ)), (y : Fin n → ℝ) ∈ (Ω : Set (Fin n → ℝ)) :=
    fun y => hVΩ y.2
  have hself : ∀ (y : Fin n → ℝ) (r : ℝ), y ∈ (Ω : Set (Fin n → ℝ)) → 0 < r →
      y ∈ rsBall (Ω : Set (Fin n → ℝ)) driftWeight X y r := fun y r hy hr =>
    ⟨hy, by rw [G1.controlDistance_self _ X hy]; exact ENNReal.ofReal_pos.2 hr⟩
  -- a finite cover of the closure by small balls and a Lebesgue radius
  obtain ⟨t, ht⟩ := hVc.elim_nhds_subcover'
    (fun y _ => rsBall (Ω : Set (Fin n → ℝ)) driftWeight X y (ρ y / 2))
    (fun y hy => (isOpen_rsBall_base Ω X hchart y _).mem_nhds
      (hself y _ (hKΩ y hy) (half_pos (hρ y (hKΩ y hy)))))
  obtain ⟨r, hr0, hrt⟩ := exists_pos_le_forall_finset t (fun y => ρ y.1 / 4)
    (fun y _ => by have := hρ y.1 (hKΩ' y); positivity)
  have hlebesgue : ∀ c ∈ closure (V : Set (Fin n → ℝ)), ∃ y ∈ t,
      rsBall (Ω : Set (Fin n → ℝ)) driftWeight X c (2 * r) ⊆ ball y.1 (ε y.1) := by
    intro c hc
    have := ht hc
    simp only [mem_iUnion] at this
    obtain ⟨y, hyt, hcy⟩ := this
    refine ⟨y, hyt, fun z hz => ?_⟩
    apply hrb y.1 (hKΩ' y)
    refine ⟨hz.1, ?_⟩
    have h2r : 2 * r ≤ ρ y.1 / 2 := by have := hrt y hyt; linarith
    calc controlDistance (Ω : Set (Fin n → ℝ)) driftWeight X y.1 z
        ≤ controlDistance (Ω : Set (Fin n → ℝ)) driftWeight X y.1 c +
          controlDistance (Ω : Set (Fin n → ℝ)) driftWeight X c z :=
          G1.controlDistance_triangle _ driftWeight X _ _ _
      _ < ENNReal.ofReal (ρ y.1 / 2) + ENNReal.ofReal (2 * r) := ENNReal.add_lt_add hcy.2 hz.2
      _ ≤ ENNReal.ofReal (ρ y.1 / 2) + ENNReal.ofReal (ρ y.1 / 2) :=
          add_le_add le_rfl (ENNReal.ofReal_le_ofReal h2r)
      _ = ENNReal.ofReal (ρ y.1) := by
          rw [← ENNReal.ofReal_add (by have := hρ y.1 (hKΩ' y); positivity)
            (by have := hρ y.1 (hKΩ' y); positivity)]
          congr 1; ring
  -- a finite net of centres at scale `r`
  obtain ⟨t2, ht2⟩ := hVc.elim_nhds_subcover'
    (fun y _ => rsBall (Ω : Set (Fin n → ℝ)) driftWeight X y r)
    (fun y hy => (isOpen_rsBall_base Ω X hchart y _).mem_nhds (hself y _ (hKΩ y hy) hr0))
  let centers : Fin t2.card → Ω := fun i =>
    ⟨((t2.equivFin.symm i : {x // x ∈ t2}).1 : closure (V : Set (Fin n → ℝ))).1,
      hKΩ' _⟩
  have hcentersK : ∀ i, (centers i).val ∈ closure (V : Set (Fin n → ℝ)) := fun i =>
    ((t2.equivFin.symm i : {x // x ∈ t2}).1).2
  have hcover2 : ∀ z ∈ closure (V : Set (Fin n → ℝ)), ∃ i,
      z ∈ rsBall (Ω : Set (Fin n → ℝ)) driftWeight X (centers i).val r := by
    intro z hz
    have := ht2 hz
    simp only [mem_iUnion] at this
    obtain ⟨c, hct, hzc⟩ := this
    refine ⟨t2.equivFin ⟨c, hct⟩, ?_⟩
    have : (centers (t2.equivFin ⟨c, hct⟩)).val = c.1 := by
      simp [centers]
    rw [this]
    exact hzc
  -- a relatively compact patch containing all `2r`-balls of the centres
  let Kc : Set (Fin n → ℝ) := ⋃ y ∈ t, closedBall y.1 (ε y.1)
  have hKc : IsCompact Kc :=
    (t.finite_toSet).isCompact_biUnion (fun y _ => isCompact_closedBall _ _)
  have hKcΩ : Kc ⊆ (Ω : Set (Fin n → ℝ)) :=
    iUnion₂_subset fun y _ => hcb y.1 (hKΩ' y)
  let V' : Set (Fin n → ℝ) := ⋃ y ∈ t, ball y.1 (ε y.1)
  have hV'Kc : V' ⊆ Kc := iUnion₂_mono fun y _ => ball_subset_closedBall
  have hV'c : IsCompact (closure V') :=
    hKc.of_isClosed_subset isClosed_closure (closure_minimal hV'Kc hKc.isClosed)
  have hV'Ω : closure V' ⊆ (Ω : Set (Fin n → ℝ)) :=
    (closure_minimal hV'Kc hKc.isClosed).trans hKcΩ
  obtain ⟨κ, hκ⟩ := RothschildStein.S.exists_controlDistance_comparison_on_compact_patch Ω
    driftWeight X hw (fun i => (hX i).continuousOn) hV'c hV'Ω
  have hballs : ∀ i, {z | z ∈ (Ω : Set (Fin n → ℝ)) ∧
      G.d (centers i).val z < ENNReal.ofReal (2 * r)} ⊆ V' := by
    intro i z hz
    obtain ⟨y, hyt, hsub⟩ := hlebesgue (centers i).val (hcentersK i)
    exact mem_biUnion hyt (hsub hz)
  obtain ⟨ζ, hζ, hsum⟩ := RothschildStein.S.exists_finite_control_ball_partition Ω G centers hr0
    hα hα1 V' hV'c hV'Ω hκ hballs
  have hfinD : ∀ i, holderENorm G.d α {z | z ∈ (Ω : Set (Fin n → ℝ)) ∧
      G.d (centers i).val z < ENNReal.ofReal (2 * r)} f < ⊤ := by
    intro i
    obtain ⟨y, hyt, hsub⟩ := hlebesgue (centers i).val (hcentersK i)
    exact lt_of_le_of_lt (RothschildStein.S.holderENorm_mono G.d α (ball y.1 (ε y.1)) f
      (fun z hz => hsub hz)) (hfin y.1 (hKΩ' y))
  have hU : (V : Set (Fin n → ℝ)) ⊆ ⋃ i, {z | z ∈ (Ω : Set (Fin n → ℝ)) ∧
      G.d (centers i).val z < ENNReal.ofReal (2 * r)} := by
    intro z hz
    obtain ⟨i, hi⟩ := hcover2 z (subset_closure hz)
    refine mem_iUnion.2 ⟨i, hi.1, lt_of_lt_of_le hi.2 (ENNReal.ofReal_le_ofReal (by linarith))⟩
  have hpart : ∀ z ∈ (V : Set (Fin n → ℝ)), ∑ i, ζ i z = 1 := by
    intro z hz
    obtain ⟨i, hi⟩ := hcover2 z (subset_closure hz)
    exact hsum z (mem_iUnion.2 ⟨i, hi⟩)
  have hcov := RothschildStein.S.holderENorm_finite_partition_cover_le Ω G driftWeight X hG hw
    centers (ENNReal.ofReal (2 * r)) hα f ζ (fun i => (hζ i).2.1) (fun i => (hζ i).2.2.1) hfinD
    (fun i => (hζ i).2.2.2) hU hpart
  exact lt_of_le_of_lt hcov (ENNReal.mul_lt_top
    (ENNReal.add_lt_top.2 ⟨ENNReal.one_lt_top,
      ENNReal.sum_lt_top.2 fun i _ => (hζ i).2.2.2⟩)
    (ENNReal.sum_lt_top.2 fun i _ => hfinD i))

end Geometry

end RothschildStein.P2

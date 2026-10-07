-- Copyright (c) 2026 Scott Armstrong and Amélie Loher. All rights reserved.
-- Released under Apache 2.0 license as described in the file LICENSE.
module

public import Mathlib.MeasureTheory.Covering.Vitali
public import Mathlib.MeasureTheory.Measure.Typeclasses.SFinite
public import Mathlib.Topology.Algebra.InfiniteSum.ENNReal

@[expose] public section

set_option autoImplicit false
set_option relaxedAutoImplicit false

open Set Metric MeasureTheory
open scoped ENNReal

namespace RothschildStein.H2

/-- Fivefold Vitali selection with the measure bound, under explicit
ball-measure hypotheses (BB Lemma 7.23, pp. 312–313). Countability follows
from positive measures and a finite-measure enclosing set. -/
theorem exists_countable_disjoint_ball_cover
    {X ι : Type*} [PseudoMetricSpace X] [MeasurableSpace X] [OpensMeasurableSpace X]
    (μ : Measure X) (t : Set ι) (z : ι → X) (r : ι → ℝ) (ρ : ℝ)
    (W : Set X) (C : ℝ≥0∞)
    (hr : ∀ i ∈ t, 0 < r i ∧ r i ≤ ρ)
    (hW : μ W < ⊤)
    (hinside : ∀ i ∈ t, ball (z i) (r i) ⊆ W)
    (hpos : ∀ i ∈ t, 0 < μ (ball (z i) (r i)))
    (hfive : ∀ i ∈ t, μ (ball (z i) (5 * r i)) ≤ C * μ (ball (z i) (r i))) :
    ∃ u ⊆ t, u.Countable ∧ u.PairwiseDisjoint (fun i => ball (z i) (r i)) ∧
      (⋃ i ∈ t, ball (z i) (r i)) ⊆ ⋃ i ∈ u, ball (z i) (5 * r i) ∧
      μ (⋃ i ∈ t, ball (z i) (r i)) ≤ C * ∑' i : u, μ (ball (z i) (r i)) := by
  classical
  obtain ⟨u, hut, hdisj, hcover⟩ :=
    Vitali.exists_disjoint_subfamily_covering_enlargement_ball
      t z r ρ (fun i hi => (hr i hi).2) 5 (by norm_num)
  have hfinite : μ (⋃ i : u, ball (z i) (r i)) ≠ ⊤ := by
    apply ne_of_lt
    exact (measure_mono (show (⋃ i : u, ball (z i) (r i)) ⊆ W from
      iUnion_subset fun (i : u) => hinside i (hut i.property))).trans_lt hW
  have hc := μ.countable_meas_pos_of_disjoint_of_meas_iUnion_ne_top
    (fun i : u => isOpen_ball.measurableSet) (hdisj.subtype _ _) hfinite
  have huCountable : u.Countable := by
    have heq : {i : u | 0 < μ (ball (z i) (r i))} = univ := by
      ext i
      simp only [mem_ofPred_eq, mem_univ, iff_true]
      exact hpos i (hut i.property)
    rw [heq] at hc
    exact Set.countable_coe_iff.mp (Set.countable_univ_iff.mp hc)
  have hcov : (⋃ i ∈ t, ball (z i) (r i)) ⊆ ⋃ i ∈ u, ball (z i) (5 * r i) := by
    intro x hx
    obtain ⟨i, hi, hxi⟩ := mem_iUnion₂.mp hx
    obtain ⟨j, hj, hij⟩ := hcover i hi
    exact mem_iUnion₂.mpr ⟨j, hj, hij hxi⟩
  refine ⟨u, hut, huCountable, hdisj, hcov, ?_⟩
  let : Countable u := huCountable.to_subtype
  have hcov' : (⋃ i ∈ t, ball (z i) (r i)) ⊆ ⋃ i : u, ball (z i) (5 * r i) := by
    intro x hx
    obtain ⟨i, hi, hxi⟩ := mem_iUnion₂.mp (hcov hx)
    exact mem_iUnion.mpr ⟨⟨i, hi⟩, hxi⟩
  calc
    μ (⋃ i ∈ t, ball (z i) (r i)) ≤ μ (⋃ i : u, ball (z i) (5 * r i)) :=
      measure_mono hcov'
    _ ≤ ∑' i : u, μ (ball (z i) (5 * r i)) := measure_iUnion_le _
    _ ≤ ∑' i : u, C * μ (ball (z i) (r i)) :=
      ENNReal.tsum_le_tsum fun i => hfive i (hut i.property)
    _ = C * ∑' i : u, μ (ball (z i) (r i)) := ENNReal.tsum_mul_left

/-- The fivefold ball bound uses only doubling up to six times the patch radius (BB Lemma 7.23, p. 312, equation (7.20)). -/
theorem measure_ball_five_le
    {X : Type*} [PseudoMetricSpace X] [MeasurableSpace X]
    (μ : Measure X) (z : X) (r ρ : ℝ) (C : ℝ≥0∞)
    (hr : 0 < r) (hrρ : r ≤ ρ)
    (hdoubling : ∀ s : ℝ, 0 < s → s ≤ 6 * ρ →
      μ (ball z s) ≤ C * μ (ball z (s / 2))) :
    μ (ball z (5 * r)) ≤ C ^ 3 * μ (ball z r) := by
  have h1 := hdoubling (5 * r) (by linarith) (by linarith)
  have h2 := hdoubling (5 * r / 2) (by linarith) (by linarith)
  have h3 := hdoubling (5 * r / 2 / 2) (by linarith) (by linarith)
  have h4 : μ (ball z (5 * r / 2 / 2 / 2)) ≤ μ (ball z r) :=
    measure_mono (ball_subset_ball (by linarith))
  calc
    μ (ball z (5 * r)) ≤ C * μ (ball z (5 * r / 2)) := h1
    _ ≤ C * (C * (C * μ (ball z r))) := by
      gcongr
      calc
        μ (ball z (5 * r / 2)) ≤ C * μ (ball z (5 * r / 2 / 2)) := h2
        _ ≤ C * (C * μ (ball z (5 * r / 2 / 2 / 2))) := by gcongr
        _ ≤ C * (C * μ (ball z r)) := by gcongr
    _ = C ^ 3 * μ (ball z r) := by simp [pow_succ, mul_assoc]

/-- Adapter from the explicit doubling-patch clauses P1–P3:
countable disjoint selection, fivefold coverage, and the C_D cubed bound
(BB Lemma 7.23, pp. 312–313). Compactness and absence of atoms are not
needed for this covering result. -/
theorem vitali_covering_of_patch_hypotheses
    {X ι : Type*} [PseudoMetricSpace X] [MeasurableSpace X] [OpensMeasurableSpace X]
    (μ : Measure X) (S W : Set X) (ρ C : ℝ)
    (hρ : 0 < ρ) (_hC : 1 < C)
    (hinside : ∀ z ∈ S, ball z (6 * ρ) ⊆ W)
    (hballs : ∀ z ∈ S, ∀ s : ℝ, 0 < s → s ≤ 6 * ρ →
      0 < μ (ball z s) ∧ μ (ball z s) < ⊤ ∧
        μ (ball z s) ≤ ENNReal.ofReal C * μ (ball z (s / 2)))
    (hW : MeasurableSet W ∧ μ W < ⊤)
    (t : Set ι) (z : ι → X) (r : ι → ℝ)
    (hz : ∀ i ∈ t, z i ∈ S) (hr : ∀ i ∈ t, 0 < r i ∧ r i ≤ ρ) :
    ∃ u ⊆ t, u.Countable ∧ u.PairwiseDisjoint (fun i => ball (z i) (r i)) ∧
      (⋃ i ∈ t, ball (z i) (r i)) ⊆ ⋃ i ∈ u, ball (z i) (5 * r i) ∧
      μ (⋃ i ∈ t, ball (z i) (r i)) ≤
        (ENNReal.ofReal C) ^ 3 * ∑' i : u, μ (ball (z i) (r i)) := by
  apply exists_countable_disjoint_ball_cover μ t z r ρ W ((ENNReal.ofReal C) ^ 3) hr hW.2
  · intro i hi
    exact (ball_subset_ball (by linarith [(hr i hi).2])).trans (hinside (z i) (hz i hi))
  · intro i hi
    exact (hballs (z i) (hz i hi) (r i) (hr i hi).1 (by linarith [(hr i hi).2])).1
  · intro i hi
    exact measure_ball_five_le μ (z i) (r i) ρ (ENNReal.ofReal C) (hr i hi).1
      (hr i hi).2 (fun s hs hsρ => (hballs (z i) (hz i hi) s hs hsρ).2.2)

end RothschildStein.H2

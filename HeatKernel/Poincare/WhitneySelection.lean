-- Copyright (c) 2026 Scott Armstrong and Amélie Loher. All rights reserved.
-- Released under Apache 2.0 license as described in the file LICENSE.
module

public import Mathlib.MeasureTheory.Covering.Vitali
public import Mathlib.Topology.MetricSpace.HausdorffDistance
public import Mathlib.Topology.Bases
public import Mathlib.Tactic.FieldSimp
public import Mathlib.Tactic.Linarith

/-! Countable Whitney ball selection in a separable metric space. -/

@[expose] public section
set_option autoImplicit false
set_option relaxedAutoImplicit false
noncomputable section
open TopologicalSpace Set Metric

namespace HeatKernel

/-- A bounded family of boundary-distance balls has a countable disjoint subfamily whose
fivefold dilates cover the open set and whose eightyfold dilates remain inside it. -/
theorem exists_countable_disjoint_boundaryBall_cover {E : Type*} [MetricSpace E]
    [SeparableSpace E] {U : Set E} (hU : IsOpen U) (hcompl : Uᶜ.Nonempty)
    {κ R : ℝ} (hκ : 80 < κ)
    (hbounded : ∀ x ∈ U, infDist x Uᶜ / κ ≤ R) :
    ∃ C : Set E, C ⊆ U ∧ C.Countable ∧
      (C.PairwiseDisjoint fun x => ball x (infDist x Uᶜ / κ)) ∧
      U = ⋃ x ∈ C, ball x (5 * (infDist x Uᶜ / κ)) ∧
      ∀ x ∈ C, ball x (80 * (infDist x Uᶜ / κ)) ⊆ U := by
  have hkpos : 0 < κ := by linarith
  have hpos : ∀ x ∈ U, 0 < infDist x Uᶜ / κ := by
    intro x hx
    apply div_pos _ hkpos
    exact (hU.isClosed_compl.notMem_iff_infDist_pos hcompl).mp (by simpa using hx)
  obtain ⟨C, hCU, hdisj, hcover⟩ :=
    Vitali.exists_disjoint_subfamily_covering_enlargement_ball U id
      (fun x => infDist x Uᶜ / κ) R hbounded 5 (by norm_num)
  have hinside : ∀ x ∈ C, ball x (80 * (infDist x Uᶜ / κ)) ⊆ U := by
    intro x hx
    apply (ball_subset_ball ?_).trans ball_infDist_compl_subset
    have hp := (hpos x (hCU hx)).le
    have he : κ * (infDist x Uᶜ / κ) = infDist x Uᶜ := by field_simp [hkpos.ne']
    nlinarith
  refine ⟨C, hCU, hdisj.countable_of_isOpen (fun _ _ => isOpen_ball)
    (fun x hx => ⟨x, mem_ball_self (hpos x (hCU hx))⟩), hdisj, ?_, hinside⟩
  apply Subset.antisymm
  · intro x hx
    obtain ⟨y, hy, hxy⟩ := hcover x hx
    exact mem_iUnion₂.mpr ⟨y, hy, hxy (mem_ball_self (hpos x hx))⟩
  · intro z hz
    obtain ⟨x, hx, hz⟩ := mem_iUnion₂.mp hz
    apply hinside x hx
    exact ball_subset_ball (by nlinarith [(hpos x (hCU hx)).le]) hz

end HeatKernel

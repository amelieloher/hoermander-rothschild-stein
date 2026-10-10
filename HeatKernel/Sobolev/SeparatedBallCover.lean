-- Copyright (c) 2026 Scott Armstrong and Amélie Loher. All rights reserved.
-- Released under Apache 2.0 license as described in the file LICENSE.
module

public import Mathlib.Topology.Bases
public import Mathlib.Topology.MetricSpace.Basic
public import Mathlib.Order.Zorn
import Mathlib.Tactic

/-! # Countable equal-radius ball covers with disjoint half-radius balls -/

@[expose] public section
open Set Metric TopologicalSpace
namespace HeatKernel.Sobolev

/-- A positive separation radius admits a maximal separated set covering by open balls. -/
theorem exists_separated_ball_cover {α : Type*} [PseudoMetricSpace α]
    {s : ℝ} (hs : 0 < s) :
    ∃ S : Set α, S.Pairwise (fun x y => s ≤ dist x y) ∧
      ∀ x : α, ∃ y ∈ S, dist x y < s := by
  obtain ⟨S, hS, hmax⟩ := zorn_subset {S : Set α | S.Pairwise (fun x y => s ≤ dist x y)} (by
    intro c hc hchain
    refine ⟨⋃₀ c, ?_, fun t ht => subset_sUnion_of_mem ht⟩
    intro x hx y hy hne
    obtain ⟨A, hA, hxA⟩ := mem_sUnion.mp hx
    obtain ⟨B, hB, hyB⟩ := mem_sUnion.mp hy
    rcases hchain.total hA hB with hAB | hBA
    · exact hc hB (hAB hxA) hyB hne
    · exact hc hA hxA (hBA hyB) hne)
  refine ⟨S, hS, fun x => ?_⟩
  by_contra! h
  have hnot : x ∉ S := by
    intro hx
    exact (not_le_of_gt hs) (by simpa only [dist_self] using h x hx)
  have hinsert : (insert x S).Pairwise (fun y z => s ≤ dist y z) := by
    intro y hy z hz hyz
    rcases mem_insert_iff.mp hy with hyx | hyS
    · subst y
      rcases mem_insert_iff.mp hz with rfl | hz
      · exact (hyz rfl).elim
      · exact h z hz
    · rcases mem_insert_iff.mp hz with rfl | hz
      · simpa only [dist_comm] using h y hyS
      · exact hS hyS hz hyz
  exact hnot (hmax hinsert (subset_insert x S) (mem_insert x S))

/-- Separated centers give disjoint half-radius open balls. -/
theorem pairwiseDisjoint_half_radius_balls {α : Type*} [PseudoMetricSpace α]
    {S : Set α} {s : ℝ} (hS : S.Pairwise (fun x y => s ≤ dist x y)) :
    S.PairwiseDisjoint (fun x => ball x (s / 2)) := by
  intro x hx y hy hxy
  apply Set.disjoint_left.mpr
  intro z hzx hzy
  have hdist := dist_triangle x z y
  rw [mem_ball, dist_comm z x] at hzx
  rw [mem_ball] at hzy
  have := hS hx hy hxy
  linarith

/-- In a separable metric space the separated equal-radius cover is countable. -/
theorem exists_countable_disjoint_half_radius_ball_cover {α : Type*}
    [PseudoMetricSpace α] [SeparableSpace α] {s : ℝ} (hs : 0 < s) :
    ∃ S : Set α, S.Countable ∧
      S.PairwiseDisjoint (fun x => ball x (s / 2)) ∧
      (⋃ x ∈ S, ball x s) = univ := by
  obtain ⟨S, hS, hcover⟩ := exists_separated_ball_cover (α := α) hs
  have hdisj := pairwiseDisjoint_half_radius_balls hS
  refine ⟨S, hdisj.countable_of_isOpen (fun _ _ => isOpen_ball)
    (fun x _ => ⟨x, mem_ball_self (by linarith)⟩), hdisj, ?_⟩
  apply eq_univ_of_forall
  intro x
  obtain ⟨y, hy, hxy⟩ := hcover x
  exact mem_iUnion.mpr ⟨y, mem_iUnion.mpr ⟨hy, by simpa only [mem_ball] using hxy⟩⟩

end HeatKernel.Sobolev

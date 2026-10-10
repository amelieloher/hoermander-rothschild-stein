-- Copyright (c) 2026 Scott Armstrong and Amélie Loher. All rights reserved.
-- Released under Apache 2.0 license as described in the file LICENSE.
module

public import Mathlib.Topology.Compactness.SigmaCompact
public import Mathlib.Topology.Sets.Opens
public import Mathlib.MeasureTheory.Function.LpSeminorm.Basic
import Mathlib.Tactic.Linter

/-! # Joint measurability from square integrability on compact subsets -/

@[expose] public section
open Set MeasureTheory TopologicalSpace
namespace HeatKernel

/-- Local square integrability on all compact subsets of an open set implies
almost everywhere strong measurability on that open set. -/
theorem aestronglyMeasurable_restrict_open_of_memLp_compacts {α : Type*}
    [TopologicalSpace α] [LocallyCompactSpace α] [SecondCountableTopology α]
    [MeasurableSpace α] (μ : Measure α) (U : Opens α) {f : α → ℝ}
    (hf : ∀ K : Set α, IsCompact K → K ⊆ (U : Set α) → MemLp f 2 (μ.restrict K)) :
    AEStronglyMeasurable f (μ.restrict (U : Set α)) := by
  let : LocallyCompactSpace (U : Set α) := U.isOpen.isOpenEmbedding_subtypeVal.locallyCompactSpace
  let K : ℕ → Set (U : Set α) := compactCovering (U : Set α)
  let S : ℕ → Set α := fun n => Subtype.val '' K n
  have hcover : ⋃ n, S n = (U : Set α) := by
    ext x
    constructor
    · intro hx
      obtain ⟨n, hn⟩ := mem_iUnion.mp hx
      obtain ⟨y, _, rfl⟩ := hn
      exact y.property
    · intro hx
      obtain ⟨n, hn⟩ := exists_mem_compactCovering (⟨x, hx⟩ : (U : Set α))
      exact mem_iUnion.mpr ⟨n, ⟨⟨x, hx⟩, hn, rfl⟩⟩
  rw [← hcover, aestronglyMeasurable_iUnion_iff]
  intro n
  apply (hf (S n) ((isCompact_compactCovering (U : Set α) n).image continuous_subtype_val) ?_).aestronglyMeasurable
  rintro x ⟨y, _, rfl⟩
  exact y.property

end HeatKernel

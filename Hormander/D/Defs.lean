-- Copyright (c) 2026 Scott Armstrong and Amélie Loher. All rights reserved.
-- Released under Apache 2.0 license as described in the file LICENSE.
module

public import Mathlib.Analysis.InnerProductSpace.PiL2
public import Mathlib.Analysis.Calculus.ContDiff.Defs
public import Mathlib.Topology.Algebra.Support
public import Mathlib.Topology.NhdsSet

@[expose] public section

open Filter Topology

namespace Hormander.D

/-- The outer cutoff is one on an open neighborhood of the support of the inner cutoff. -/
def cutoffPrecedes {N : ℕ} (η η' : EuclideanSpace ℝ (Fin N) → ℝ) : Prop :=
  ContDiff ℝ (⊤ : ℕ∞) η ∧ HasCompactSupport η ∧
    ContDiff ℝ (⊤ : ℕ∞) η' ∧ HasCompactSupport η' ∧
    ∀ᶠ x in 𝓝ˢ (tsupport η), η' x = 1

/-- The neighborhood condition in `cutoffPrecedes` is equivalent to an interior inclusion
for the tempered support of the inner cutoff. -/
theorem cutoffPrecedes_eventually_iff_interior {N : ℕ}
    (η η' : EuclideanSpace ℝ (Fin N) → ℝ) :
    (∀ᶠ x in 𝓝ˢ (tsupport η), η' x = 1) ↔
      tsupport η ⊆ interior {x | η' x = 1} := by
  change {x | η' x = 1} ∈ 𝓝ˢ (tsupport η) ↔ _
  exact subset_interior_iff_mem_nhdsSet.symm

end Hormander.D

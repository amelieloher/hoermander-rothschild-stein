-- Copyright (c) 2026 Scott Armstrong and Amélie Loher. All rights reserved.
-- Released under Apache 2.0 license as described in the file LICENSE.
module

public import Mathlib.Topology.Connected.Basic
public import Mathlib.Combinatorics.SimpleGraph.Connectivity.Connected

/-! Finite simple chains in connected open covers. -/

@[expose] public section
set_option autoImplicit false
set_option relaxedAutoImplicit false
noncomputable section
open Set

namespace HeatKernel

/-- The graph of distinct intersecting members of a family of sets. -/
def intersectionGraph {E ι : Type*} (U : ι → Set E) : SimpleGraph ι where
  Adj i j := i ≠ j ∧ (U i ∩ U j).Nonempty
  symm := ⟨by
    intro i j h
    exact ⟨h.1.symm, by simpa only [inter_comm] using h.2⟩⟩
  loopless := ⟨by intro i h; exact h.1 rfl⟩

end HeatKernel

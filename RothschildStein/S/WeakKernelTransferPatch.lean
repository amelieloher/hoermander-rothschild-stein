-- Copyright (c) 2026 Scott Armstrong and Amélie Loher. All rights reserved.
-- Released under Apache 2.0 license as described in the file LICENSE.
module

public import RothschildStein.S.WeakRescaledPairing
public import RothschildStein.S.RescaledTransferIdentity
public import RothschildStein.S.CompactKernelDirectionalTest
public import RothschildStein.S.FriedrichsInteriorPatch

set_option autoImplicit false
set_option relaxedAutoImplicit false
set_option backward.isDefEq.respectTransparency false
@[expose] public section
noncomputable section
open Set MeasureTheory Function Metric TopologicalSpace
open scoped Topology ContDiff
namespace RothschildStein.S
variable {n q : ℕ}

/-- Compact containment of the closure supplies the
positive radius under the local geometric assumptions (BB pp. 75–78; domain). -/
theorem exists_friedrichs_interior_radius
    (Ω : Opens (Fin n → ℝ)) {U : Set (Fin n → ℝ)}
    (hc : IsCompact (closure U)) (hU : closure U ⊆ Ω) :
    ∃ δ : ℝ, 0 < δ ∧ cthickening δ (closure U) ⊆ Ω :=
  hc.exists_cthickening_subset_open Ω.isOpen hU

end RothschildStein.S

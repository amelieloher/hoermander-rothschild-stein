-- Copyright (c) 2026 Scott Armstrong and Amélie Loher. All rights reserved.
-- Released under Apache 2.0 license as described in the file LICENSE.
module

public import RothschildStein.H3.QuasiballDomain
public import RothschildStein.G2.GaugeConsequences

set_option autoImplicit false
set_option relaxedAutoImplicit false
set_option backward.isDefEq.respectTransparency false
@[expose] public section
namespace RothschildStein.H3
open Set TopologicalSpace

/-- The existing quasiball domain at the origin is the literal norm sublevel. -/
theorem quasiballDomain_origin_set {n : ℕ} (G : HomogeneousGroup n)
    (ν : G2.HomogeneousNorm G) (R : ℝ) :
    (quasiballDomain G ν 0 R : Set (Fin n → ℝ)) = {x | ν x < R} := by
  ext x
  change ν (G.mul (G.inv 0) x) < R ↔ ν x < R
  rw [G2.inv_zero, G2.zero_mul]

end RothschildStein.H3

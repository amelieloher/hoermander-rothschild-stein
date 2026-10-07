-- Copyright (c) 2026 Scott Armstrong and Amélie Loher. All rights reserved.
-- Released under Apache 2.0 license as described in the file LICENSE.
module

public import RothschildStein.H3.QuasiballDomain
public import RothschildStein.H3.ContinuousSublevelDomain
public import RothschildStein.G2.Algebra

set_option autoImplicit false
set_option relaxedAutoImplicit false
@[expose] public section
noncomputable section
namespace RothschildStein.H3
open Set TopologicalSpace
variable {n : ℕ}

/-- The center-zero quasiball is exactly a continuous-gauge sublevel, so
the abstract exhaustion theorem applies to the actual local domains. -/
theorem quasiballDomain_zero_eq_sublevel (G : HomogeneousGroup n)
    (ν : G2.HomogeneousNorm G) (R : ℝ) :
    quasiballDomain G ν 0 R = continuousSublevelDomain ν ν.gauge.1 R := by
  apply Opens.ext
  ext x
  change ν (G.mul (G.inv 0) x) < R ↔ ν x < R
  rw [G2.inv_zero G, G2.zero_mul G]

end RothschildStein.H3

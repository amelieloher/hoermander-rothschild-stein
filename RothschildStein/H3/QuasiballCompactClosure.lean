-- Copyright (c) 2026 Scott Armstrong and Amélie Loher. All rights reserved.
-- Released under Apache 2.0 license as described in the file LICENSE.
module

public import RothschildStein.H3.QuasiballDomain

set_option autoImplicit false
set_option relaxedAutoImplicit false
@[expose] public section
namespace RothschildStein.H3
open Set TopologicalSpace

/-- Every existing quasiball domain has compact closure, using the
proved compact closed gauge ball and continuity of left translation. -/
theorem quasiballDomain_closure_compact {n : ℕ} (G : HomogeneousGroup n)
    (ν : G2.HomogeneousNorm G) (x₀ : Fin n → ℝ) (r : ℝ) :
    IsCompact (closure (quasiballDomain G ν x₀ r : Set (Fin n → ℝ))) := by
  apply (G2.isCompact_gaugeClosedBall G ν.gauge x₀ r).of_isClosed_subset isClosed_closure
  apply closure_minimal
  · intro x hx
    change ν (G.mul (G.inv x₀) x) < r at hx
    change ν (G.mul (G.inv x₀) x) ≤ r
    exact hx.le
  · exact (isClosed_le ν.gauge.1 continuous_const).preimage
      (G2.gaugeLeftTranslation G x₀).symm.continuous

end RothschildStein.H3

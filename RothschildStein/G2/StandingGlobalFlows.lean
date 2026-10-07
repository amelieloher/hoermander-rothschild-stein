-- Copyright (c) 2026 Scott Armstrong and Amélie Loher. All rights reserved.
-- Released under Apache 2.0 license as described in the file LICENSE.
module

public import RothschildStein.G2.InvariantGlobalFlow
public import RothschildStein.H1.Standing

@[expose] public section
set_option autoImplicit false
set_option relaxedAutoImplicit false
noncomputable section
namespace RothschildStein.H1
variable {N q : ℕ} (G : HomogeneousGroup N)

/-- Global horizontal flows supplying the E/hflow hypotheses of H3. -/
theorem StandingHypotheses.exists_global_horizontal_flows (H : StandingHypotheses G q) :
    ∃ E : Fin q → ℝ → (Fin N → ℝ),
      (∀ i, Continuous (E i)) ∧ (∀ i, E i 0 = 0) ∧
      ∀ i x, IsIntegralCurve (fun t => G.mul x (E i t)) (fun _ => H.fields i.succ) :=
  G2.exists_global_leftInvariant_flows G (fun i : Fin q => H.fields i.succ)
    (fun i => H.invariant i.succ)

end RothschildStein.H1

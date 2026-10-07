-- Copyright (c) 2026 Scott Armstrong and Amélie Loher. All rights reserved.
-- Released under Apache 2.0 license as described in the file LICENSE.
module

public import RothschildStein.G2.MeasureConsequences
public import RothschildStein.G2.GaugeConsequences
public import RothschildStein.H3.ControlMetric

set_option autoImplicit false
set_option relaxedAutoImplicit false
@[expose] public section
noncomputable section
open Set MeasureTheory
namespace RothschildStein.H3
open G2
variable {N : ℕ} {G : HomogeneousGroup N}

/-- Smooth-gauge quasi-balls are open and bounded with compact closure;
the closure is contained in the compact closed quasi-ball (BB p. 578). -/
theorem quasiBall_geometry {ν : (Fin N → ℝ) → ℝ} (hν : G.IsHomogeneousGauge ν)
    (x : Fin N → ℝ) (r : ℝ) :
    IsOpen (gaugeBall G ν x r) ∧
    Bornology.IsBounded (gaugeBall G ν x r) ∧
    IsCompact (closure (gaugeBall G ν x r)) ∧
    closure (gaugeBall G ν x r) ⊆ gaugeClosedBall G ν x r := by
  have hk := isCompact_gaugeClosedBall G hν x r
  have hs : gaugeBall G ν x r ⊆ gaugeClosedBall G ν x r := by
    intro y hy
    change gaugeDistance G ν y x < r at hy
    change gaugeDistance G ν y x ≤ r
    exact hy.le
  have hcl := closure_minimal hs hk.isClosed
  exact ⟨isOpen_gaugeBall G hν x r, hk.isBounded.subset hs,
    hk.of_isClosed_subset isClosed_closure hcl, hcl⟩

end RothschildStein.H3

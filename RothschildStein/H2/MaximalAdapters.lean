-- Copyright (c) 2026 Scott Armstrong and Amélie Loher. All rights reserved.
-- Released under Apache 2.0 license as described in the file LICENSE.
module
public import RothschildStein.H2.MaximalEndpoint
@[expose] public section
set_option autoImplicit false
set_option relaxedAutoImplicit false
open Set Metric MeasureTheory Filter
open scoped ENNReal Topology
namespace RothschildStein.H2
variable {X : Type*} [MetricSpace X] [MeasurableSpace X] [BorelSpace X]

/-- The outer locally doubling patch gives the weak bound used in the Calderón–Zygmund decomposition. -/
theorem LocDoubling.outer_maximal_weak_type (D : LocDoubling X) :
    PatchMaximalWeakType D.μ D.Ω₁ D.Ω₂ D.κ D.C_D :=
  D.outerPatch.maximal_weak_type

end RothschildStein.H2

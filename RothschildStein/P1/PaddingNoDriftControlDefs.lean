-- Copyright (c) 2026 Scott Armstrong and Amélie Loher. All rights reserved.
-- Released under Apache 2.0 license as described in the file LICENSE.
module

public import RothschildStein.P1.PaddingNoDriftDefs
public import RothschildStein.Definitions.isControlledCurve

set_option autoImplicit false
set_option relaxedAutoImplicit false
@[expose] public section
noncomputable section
namespace RothschildStein.P1

/-- Original no-drift controls extend by zero on every added diffusion. -/
def paddingNoDriftControlCoefficients {q d : ℕ} (a : Fin q → ℝ → ℝ) :
    Fin (q + d) → ℝ → ℝ := Fin.addCases a (fun _ => 0)

end RothschildStein.P1

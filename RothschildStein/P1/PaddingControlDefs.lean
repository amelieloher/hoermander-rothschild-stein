-- Copyright (c) 2026 Scott Armstrong and Amélie Loher. All rights reserved.
-- Released under Apache 2.0 license as described in the file LICENSE.
module

public import RothschildStein.P1.PaddingLieWordDefs
public import RothschildStein.Definitions.isControlledCurve

set_option autoImplicit false
set_option relaxedAutoImplicit false
@[expose] public section
noncomputable section
namespace RothschildStein.P1

/-- Preserve all original control weights and assign weight one
to each added diffusion. In the drift setting the original drift keeps
weight two; it is never assigned a new diffusion weight. -/
def paddingControlWeights {q d : ℕ} (w : Fin (q + 1) → ℕ+) : Fin (q + d + 1) → ℕ+ :=
  Fin.cases (w 0) (Fin.addCases (fun j => w j.succ) (fun _ : Fin d => 1))

/-- Lift original controls by appending zero controls for the
added diffusion directions; the original index zero is preserved. -/
def paddingControlCoefficients {q d : ℕ} (a : Fin (q + 1) → ℝ → ℝ) :
    Fin (q + d + 1) → ℝ → ℝ :=
  Fin.cases (a 0) (Fin.addCases (fun j => a j.succ) (fun _ : Fin d => 0))

end RothschildStein.P1

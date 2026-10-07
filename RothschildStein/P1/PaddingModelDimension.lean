-- Copyright (c) 2026 Scott Armstrong and Amélie Loher. All rights reserved.
-- Released under Apache 2.0 license as described in the file LICENSE.
module

public import RothschildStein.P1.ModelHypotheses
public import RothschildStein.P1.PaddingNoDriftDefs
public import RothschildStein.P1.PaddingControlDefs

set_option autoImplicit false
set_option relaxedAutoImplicit false
@[expose] public section
noncomputable section
open Set
namespace RothschildStein.P1

/-- Genuine diffusion padding preserves the canonical
all-one no-drift weight system. -/
theorem paddingNoDriftWeights_one {q d : ℕ} :
    paddingNoDriftWeights (d := d) (fun _ : Fin q => (1 : ℕ+)) =
      fun _ => (1 : ℕ+) := by
  funext i
  refine Fin.addCases (fun _ => ?_) (fun _ => ?_) i <;>
    simp [paddingNoDriftWeights]

/-- Genuine diffusion padding preserves the canonical drift
weight two and diffusion weights one. -/
theorem paddingControlWeights_canonical {q d : ℕ} :
    paddingControlWeights (d := d)
      (fun i : Fin (q + 1) => if i = 0 then (2 : ℕ+) else 1) =
      fun i : Fin (q + d + 1) => if i = 0 then (2 : ℕ+) else 1 := by
  funext i
  refine Fin.cases ?_ (fun j => ?_) i
  · simp [paddingControlWeights]
  · refine Fin.addCases (fun _ => ?_) (fun _ => ?_) j <;>
      simp [paddingControlWeights]

end RothschildStein.P1

-- Copyright (c) 2026 Scott Armstrong and Amélie Loher. All rights reserved.
-- Released under Apache 2.0 license as described in the file LICENSE.
module
public import RothschildStein.L1.FrameValueEquiv
@[expose] public section
set_option autoImplicit false
set_option relaxedAutoImplicit false
noncomputable section
open Filter
open scoped Topology
namespace RothschildStein.L1

/-- One chosen tangent frame remains a frame on a neighborhood
of the base point, because its actual field values vary continuously. -/
theorem frame_linearIndependent_eventually {N : ℕ}
    (Y : Fin N → (Fin N → ℝ) → (Fin N → ℝ)) (x : Fin N → ℝ)
    (hY : ∀ i, ContinuousAt (Y i) x)
    (hframe : LinearIndependent ℝ (fun i => Y i x)) :
    ∀ᶠ y in 𝓝 x, LinearIndependent ℝ (fun i => Y i y) := by
  have hc : ContinuousAt (fun y i => Y i y) x := continuousAt_pi.mpr hY
  exact hc.preimage_mem_nhds (isOpen_setOfPred_linearIndependent.mem_nhds hframe)
end RothschildStein.L1

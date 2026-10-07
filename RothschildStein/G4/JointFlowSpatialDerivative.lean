-- Copyright (c) 2026 Scott Armstrong and Amélie Loher. All rights reserved.
-- Released under Apache 2.0 license as described in the file LICENSE.
module

public import RothschildStein.G4.PartialSpatialJets

@[expose] public section
set_option autoImplicit false
set_option relaxedAutoImplicit false
noncomputable section
open Set
open scoped Topology

namespace RothschildStein.G4

/-- The spatial Jacobian of a jointly smooth parameter/time flow
is jointly smooth on its actual open domain (BB pp. 441–443). -/
theorem joint_flow_spatial_fderiv_contDiffOn {P E : Type*}
    [NormedAddCommGroup P] [NormedSpace ℝ P]
    [NormedAddCommGroup E] [NormedSpace ℝ E]
    {S : Set ((P × E) × ℝ)} (hS : IsOpen S) {Φ : (P × E) × ℝ → E}
    (hΦ : ContDiffOn ℝ (⊤ : ℕ∞) Φ S) :
    ContDiffOn ℝ (⊤ : ℕ∞)
      (fun q => fderiv ℝ (fun y => Φ ((q.1.1, y), q.2)) q.1.2) S := by
  let I : E →L[ℝ] ((P × E) × ℝ) :=
    (ContinuousLinearMap.inl ℝ (P × E) ℝ).comp (ContinuousLinearMap.inr ℝ P E)
  let L := (ContinuousLinearMap.compL ℝ E ((P × E) × ℝ) E).flip I
  apply hS.contDiffOn_iff.mpr
  intro q hq
  have hfull : ContDiffAt ℝ (⊤ : ℕ∞) (fderiv ℝ Φ) q :=
    (hΦ.contDiffAt (hS.mem_nhds hq)).fderiv_right (by simp)
  apply (hfull.continuousLinearMap_comp L).congr_of_eventuallyEq
  filter_upwards [hS.mem_nhds hq] with p hp
  have hh := (((hΦ.contDiffAt (hS.mem_nhds hp)).differentiableAt
    (by simp)).hasFDerivAt.comp p.1 (hasFDerivAt_prodMk_left (𝕜 := ℝ) p.1 p.2)).comp
      p.1.2 (hasFDerivAt_prodMk_right (𝕜 := ℝ) p.1.1 p.1.2)
  change fderiv ℝ (fun y => Φ ((p.1.1, y), p.2)) p.1.2 = (fderiv ℝ Φ p).comp I
  simpa only [Function.comp_def, I, ContinuousLinearMap.comp_assoc] using hh.fderiv

end RothschildStein.G4

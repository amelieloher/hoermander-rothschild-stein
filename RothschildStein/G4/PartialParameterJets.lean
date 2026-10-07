-- Copyright (c) 2026 Scott Armstrong and Amélie Loher. All rights reserved.
-- Released under Apache 2.0 license as described in the file LICENSE.
module

public import RothschildStein.G4.AffineJetBounds

@[expose] public section
set_option autoImplicit false
set_option relaxedAutoImplicit false
noncomputable section
open Set
open scoped Topology

namespace RothschildStein.G4

/-- A stationary parameter slice derivative is restriction of the full joint
derivative to the spatial coordinate (BB Lemma 9.48, pp. 441–443). -/
theorem fderiv_parameter_slice_eq_full_comp {P E F : Type*}
    [NormedAddCommGroup P] [NormedSpace ℝ P]
    [NormedAddCommGroup E] [NormedSpace ℝ E]
    [NormedAddCommGroup F] [NormedSpace ℝ F]
    {W : P × E → F} {p : P × E} (hW : DifferentiableAt ℝ W p) :
    fderiv ℝ (fun y => W (y, p.2)) p.1 =
      (fderiv ℝ W p).comp (ContinuousLinearMap.inl ℝ P E) := by
  exact (hW.hasFDerivAt.comp p.1 (hasFDerivAt_prodMk_left p.1 p.2)).fderiv

/-- Parameter derivatives of jointly smooth flow families are jointly
smooth on the actual open domain (BB Lemma 9.48, pp. 441–443). -/
theorem partial_parameter_fderiv_contDiffOn {P E F : Type*}
    [NormedAddCommGroup P] [NormedSpace ℝ P]
    [NormedAddCommGroup E] [NormedSpace ℝ E]
    [NormedAddCommGroup F] [NormedSpace ℝ F]
    {S : Set (P × E)} (hS : IsOpen S) {W : P × E → F}
    (hW : ContDiffOn ℝ (⊤ : ℕ∞) W S) :
    ContDiffOn ℝ (⊤ : ℕ∞) (fun p => fderiv ℝ (fun y => W (y, p.2)) p.1) S := by
  apply hS.contDiffOn_iff.mpr
  intro p hp
  let L := (ContinuousLinearMap.compL ℝ P (P × E) F).flip
    (ContinuousLinearMap.inl ℝ P E)
  have hs := hW.contDiffAt (hS.mem_nhds hp)
  have hfull : ContDiffAt ℝ (⊤ : ℕ∞) (fderiv ℝ W) p := hs.fderiv_right (by simp)
  have hh := hfull.continuousLinearMap_comp L
  apply hh.congr_of_eventuallyEq
  filter_upwards [hS.mem_nhds hp] with q hq
  exact fderiv_parameter_slice_eq_full_comp
    ((hW.contDiffAt (hS.mem_nhds hq)).differentiableAt (by simp))

end RothschildStein.G4

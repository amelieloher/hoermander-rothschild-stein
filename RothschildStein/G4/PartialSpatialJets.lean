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

/-- A spatial slice derivative is restriction of the full joint
derivative to the spatial coordinate (BB Lemma 9.48, pp. 441–443). -/
theorem fderiv_spatial_slice_eq_full_comp {P E F : Type*}
    [NormedAddCommGroup P] [NormedSpace ℝ P]
    [NormedAddCommGroup E] [NormedSpace ℝ E]
    [NormedAddCommGroup F] [NormedSpace ℝ F]
    {W : P × E → F} {p : P × E} (hW : DifferentiableAt ℝ W p) :
    fderiv ℝ (fun y => W (p.1, y)) p.2 =
      (fderiv ℝ W p).comp (ContinuousLinearMap.inr ℝ P E) := by
  exact (hW.hasFDerivAt.comp p.2 (hasFDerivAt_prodMk_right p.1 p.2)).fderiv

/-- Spatial derivatives of jointly smooth field families are jointly
smooth on the actual open domain (BB Lemma 9.48, pp. 441–443). -/
theorem partial_spatial_fderiv_contDiffOn {P E F : Type*}
    [NormedAddCommGroup P] [NormedSpace ℝ P]
    [NormedAddCommGroup E] [NormedSpace ℝ E]
    [NormedAddCommGroup F] [NormedSpace ℝ F]
    {S : Set (P × E)} (hS : IsOpen S) {W : P × E → F}
    (hW : ContDiffOn ℝ (⊤ : ℕ∞) W S) :
    ContDiffOn ℝ (⊤ : ℕ∞) (fun p => fderiv ℝ (fun y => W (p.1, y)) p.2) S := by
  apply hS.contDiffOn_iff.mpr
  intro p hp
  let L := (ContinuousLinearMap.compL ℝ E (P × E) F).flip
    (ContinuousLinearMap.inr ℝ P E)
  have hs := hW.contDiffAt (hS.mem_nhds hp)
  have hfull : ContDiffAt ℝ (⊤ : ℕ∞) (fderiv ℝ W) p := hs.fderiv_right (by simp)
  have hh := hfull.continuousLinearMap_comp L
  apply hh.congr_of_eventuallyEq
  filter_upwards [hS.mem_nhds hp] with q hq
  exact fderiv_spatial_slice_eq_full_comp
    ((hW.contDiffAt (hS.mem_nhds hq)).differentiableAt (by simp))

/-- A full jet of the spatial derivative is bounded by the next
full joint jet, with no loss of coefficient-norm factors
(BB Lemma 9.48, pp. 441–443). -/
theorem norm_partial_spatial_fderiv_jet_le {P E F : Type*}
    [NormedAddCommGroup P] [NormedSpace ℝ P]
    [NormedAddCommGroup E] [NormedSpace ℝ E]
    [NormedAddCommGroup F] [NormedSpace ℝ F]
    {S : Set (P × E)} (hS : IsOpen S) {W : P × E → F}
    (hW : ContDiffOn ℝ (⊤ : ℕ∞) W S) {p : P × E} (hp : p ∈ S) (n : ℕ) :
    ‖iteratedFDeriv ℝ n (fun q => fderiv ℝ (fun y => W (q.1, y)) q.2) p‖ ≤
      ‖iteratedFDeriv ℝ (n + 1) W p‖ := by
  let L : ((P × E) →L[ℝ] F) →L[ℝ] (E →L[ℝ] F) :=
    (ContinuousLinearMap.compL ℝ E (P × E) F).flip (ContinuousLinearMap.inr ℝ P E)
  have hL : ‖L‖ ≤ 1 := by
    apply ContinuousLinearMap.opNorm_le_bound L (by norm_num)
    intro D
    simp only [one_mul]
    apply ContinuousLinearMap.opNorm_le_bound _ (norm_nonneg D)
    intro v
    simpa [L] using D.le_opNorm (0, v)
  have he : (fun q => fderiv ℝ (fun y => W (q.1, y)) q.2) =ᶠ[𝓝 p] L ∘ fderiv ℝ W := by
    filter_upwards [hS.mem_nhds hp] with q hq
    exact fderiv_spatial_slice_eq_full_comp
      ((hW.contDiffAt (hS.mem_nhds hq)).differentiableAt (by simp))
  rw [(he.iteratedFDeriv ℝ n).eq_of_nhds]
  have hfull : ContDiffAt ℝ (⊤ : ℕ∞) (fderiv ℝ W) p :=
    (hW.contDiffAt (hS.mem_nhds hp)).fderiv_right (by simp)
  have hh := L.norm_iteratedFDeriv_comp_left (x := p) hfull (n := n) (by simp)
  apply hh.trans
  rw [norm_iteratedFDeriv_fderiv]
  exact (mul_le_mul_of_nonneg_right hL (norm_nonneg _)).trans_eq (one_mul _)

end RothschildStein.G4

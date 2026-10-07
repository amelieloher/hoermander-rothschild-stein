-- Copyright (c) 2026 Scott Armstrong and Amélie Loher. All rights reserved.
-- Released under Apache 2.0 license as described in the file LICENSE.
module

public import RothschildStein.S.RescaledKernelDifferentiation
public import Mathlib.Topology.MetricSpace.Thickening

set_option autoImplicit false
set_option relaxedAutoImplicit false
set_option backward.isDefEq.respectTransparency false
@[expose] public section
noncomputable section
open Set MeasureTheory Function Metric TopologicalSpace
open scoped Topology ContDiff
namespace RothschildStein.S
variable {n : ℕ}

/-- On an interior patch the Friedrichs kernel operator is smooth for locally integrable inputs (BB p. 76). -/
theorem contDiffOn_friedrichsKernelOp_interior_patch
    (Ω : Opens (Fin n → ℝ)) (K : SmoothFriedrichsKernel n)
    {U : Set (Fin n → ℝ)} (hU : IsOpen U) (hc : IsCompact (closure U))
    {δ ε : ℝ} (hε : 0 < ε) (hεδ : ε < δ)
    (hδ : cthickening δ (closure U) ⊆ Ω)
    {h : (Fin n → ℝ) → ℝ} (hh : LocallyIntegrableOn h (Ω : Set (Fin n → ℝ)) volume) :
    ContDiffOn ℝ (⊤ : ℕ∞) (friedrichsKernelOp K.family h ε) U := by
  have hks : ∀ x z, x ∈ U → z ∉ cthickening δ (closure U) →
      friedrichsRescaledKernel K.family ε x z = 0 := by
    intro x z hx hz
    apply friedrichsRescaledKernel_eq_zero_of_dist K hε
    by_contra hn
    exact hz (mem_cthickening_of_dist_le z x δ (closure U) (subset_closure hx)
      ((le_of_not_gt hn).trans hεδ.le))
  have H := contDiffOn_compactKernelIntegral_of_local_data Ω
    ⟨cthickening δ (closure U),hc.cthickening⟩ hδ hU hks
    (contDiff_friedrichsRescaledKernel K ε).contDiffOn hh
  have he : friedrichsKernelOp K.family h ε =
      fun x => ∫ z, h z * friedrichsRescaledKernel K.family ε x z := by
    funext x
    exact friedrichsKernelOp_eq_rescaled K.family h hε x
  rw [he]
  exact H

/-- The standing interior thickening supplies the common support
ball required by weak transfer, at every scale ε<δ (BB p. 78). -/
theorem closedBall_subset_of_interior_thickening
    (Ω : Opens (Fin n → ℝ)) {U : Set (Fin n → ℝ)} {δ : ℝ}
    (hδ : cthickening δ (closure U) ⊆ Ω) {x : Fin n → ℝ} (hx : x ∈ U) :
    closedBall x δ ⊆ Ω := by
  intro z hz
  exact hδ (mem_cthickening_of_dist_le z x δ (closure U) (subset_closure hx) hz)

end RothschildStein.S

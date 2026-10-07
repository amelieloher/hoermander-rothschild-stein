-- Copyright (c) 2026 Scott Armstrong and Amélie Loher. All rights reserved.
-- Released under Apache 2.0 license as described in the file LICENSE.
module

public import RothschildStein.S.WeakKernelTransferGerms
public import RothschildStein.S.FriedrichsInteriorPatch

set_option autoImplicit false
set_option relaxedAutoImplicit false
set_option backward.isDefEq.respectTransparency false
@[expose] public section
noncomputable section
open Set MeasureTheory Function Filter Metric TopologicalSpace
open scoped Topology ContDiff
namespace RothschildStein.S
variable {n q : ℕ}

/-- One coefficient extension on the interior tube works
for every kernel in the word recursion, at every x and scale in the patch
(BB pp. 78–79; local representation). -/
theorem weak_friedrichsKernel_transfer_germ_patch
    (Ω : Opens (Fin n → ℝ)) (K : SmoothFriedrichsKernel n)
    (X : Fin q → (Fin n → ℝ) → (Fin n → ℝ)) (j : Fin q)
    (B : (Fin n → ℝ) → (Fin n → ℝ)) (hB : ContDiff ℝ (⊤ : ℕ∞) B)
    {h g : (Fin n → ℝ) → ℝ} (hg : hasWeakWordDeriv X Ω [j] h g)
    {U : Set (Fin n → ℝ)} {δ ε : ℝ} (hε : ε ∈ Ioo 0 δ)
    (hδ : cthickening δ (closure U) ⊆ Ω)
    (hG : ∀ z ∈ cthickening δ (closure U), B =ᶠ[𝓝 z] X j)
    {x : Fin n → ℝ} (hx : x ∈ U) :
    fieldDerivative (X j) (friedrichsKernelOp K.family h ε) x =
      friedrichsKernelOp K.family g ε x +
        friedrichsKernelOp (smoothKernelTransfer K B hB).family h ε x := by
  apply weak_friedrichsKernel_transfer_of_coefficient_germs Ω K X j B hB hg hε.1
    (sub_pos.mpr hε.2) x
  · simpa only [add_sub_cancel] using closedBall_subset_of_interior_thickening Ω hδ hx
  · intro z hz
    apply hG z
    apply mem_cthickening_of_dist_le z x δ (closure U) (subset_closure hx)
    simpa only [add_sub_cancel,mem_closedBall] using hz

end RothschildStein.S

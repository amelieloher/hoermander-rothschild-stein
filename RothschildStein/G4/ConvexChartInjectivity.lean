-- Copyright (c) 2026 Scott Armstrong and Amélie Loher. All rights reserved.
-- Released under Apache 2.0 license as described in the file LICENSE.
module

public import Mathlib.Analysis.Calculus.MeanValue
public import Mathlib.Analysis.Calculus.FDeriv.Linear

@[expose] public section
set_option autoImplicit false
set_option relaxedAutoImplicit false
noncomputable section
open Set

namespace RothschildStein.G4

/-- A derivative uniformly within a factor less than one of an
invertible reference map is injective on a convex domain. This is the
quantitative reference-chart argument (BB (9.55), p. 453). -/
theorem convex_injOn_of_normalized_derivative_bound
    {E F : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    [NormedAddCommGroup F] [NormedSpace ℝ F]
    {s : Set E} (hs : Convex ℝ s) (f : E → F) (L : E ≃L[ℝ] F)
    {c : ℝ} (hc : c < 1) (hf : ∀ x ∈ s, DifferentiableAt ℝ f x)
    (hbound : ∀ x ∈ s,
      ‖(L.symm : F →L[ℝ] E).comp (fderiv ℝ f x) - ContinuousLinearMap.id ℝ E‖ ≤ c) :
    InjOn f s := by
  let g := fun x => L.symm (f x) - x
  let g' := fun x => (L.symm : F →L[ℝ] E).comp (fderiv ℝ f x) -
    ContinuousLinearMap.id ℝ E
  have hg : ∀ x ∈ s, HasFDerivWithinAt g (g' x) s x := by
    intro x hx
    exact (((L.symm : F →L[ℝ] E).hasFDerivAt.comp x (hf x hx).hasFDerivAt).sub
      (hasFDerivAt_id x)).hasFDerivWithinAt
  intro x hx y hy hxy
  have hh := Convex.norm_image_sub_le_of_norm_hasFDerivWithin_le hg hbound hs hx hy
  have heq : g y - g x = x - y := by
    dsimp [g]
    rw [hxy]
    abel
  rw [heq, norm_sub_rev] at hh
  have hz : ‖y - x‖ = 0 := by nlinarith [norm_nonneg (y - x)]
  exact (sub_eq_zero.mp (norm_eq_zero.mp hz)).symm

end RothschildStein.G4

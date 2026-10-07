-- Copyright (c) 2026 Scott Armstrong and Amélie Loher. All rights reserved.
-- Released under Apache 2.0 license as described in the file LICENSE.
module

public import RothschildStein.P1.PaddingFieldProjections
public import Mathlib.Analysis.Calculus.FDeriv.Comp
public import Mathlib.Analysis.Calculus.VectorField

set_option autoImplicit false
set_option relaxedAutoImplicit false
set_option backward.isDefEq.respectTransparency false
@[expose] public section
noncomputable section
namespace RothschildStein.P1

/-- The derivative of an extended original field has the
original derivative in its base block and zero in its added block. -/
theorem fderiv_paddingBaseField {n d : ℕ}
    (X : (Fin n → ℝ) → (Fin n → ℝ)) (ξ v : Fin (n + d) → ℝ)
    (hX : DifferentiableAt ℝ X (paddingBaseCLM n d ξ)) :
    fderiv ℝ (paddingBaseField (d := d) X) ξ v =
      joinPoint (fderiv ℝ X (paddingBaseCLM n d ξ) (paddingBaseCLM n d v)) 0 := by
  let p := paddingBaseCLM n d
  let J : (Fin n → ℝ) →L[ℝ] (Fin (n + d) → ℝ) :=
    (paddingJoinCLM n d).comp (ContinuousLinearMap.inl ℝ _ _)
  have hJ (w : Fin n → ℝ) : J w = joinPoint w (0 : Fin d → ℝ) := by
    change paddingJoinCLM n d (w, 0) = _
    exact paddingJoinCLM_apply n d w 0
  have he : paddingBaseField (d := d) X = (J ∘ (X ∘ p)) := by
    funext w
    exact (hJ (X (p w))).symm
  have hp := hX.hasFDerivAt.comp ξ p.hasFDerivAt
  have h := J.hasFDerivAt.comp ξ hp
  rw [he, h.fderiv]
  change J (fderiv ℝ X (p ξ) (p v)) = _
  exact hJ _

/-- Lie brackets of extended original fields remain entirely
in the original block and equal the extension of the original bracket.
Only differentiability at the specified base point is required. -/
theorem lieBracket_paddingBaseField {n d : ℕ}
    (X Y : (Fin n → ℝ) → (Fin n → ℝ)) (ξ : Fin (n + d) → ℝ)
    (hX : DifferentiableAt ℝ X (paddingBaseCLM n d ξ))
    (hY : DifferentiableAt ℝ Y (paddingBaseCLM n d ξ)) :
    VectorField.lieBracket ℝ (paddingBaseField (d := d) X) (paddingBaseField (d := d) Y) ξ =
      paddingBaseField (d := d) (VectorField.lieBracket ℝ X Y) ξ := by
  change fderiv ℝ (paddingBaseField (d := d) Y) ξ (paddingBaseField (d := d) X ξ) -
    fderiv ℝ (paddingBaseField (d := d) X) ξ (paddingBaseField (d := d) Y ξ) =
    joinPoint (fderiv ℝ Y (paddingBaseCLM n d ξ) (X (paddingBaseCLM n d ξ)) -
      fderiv ℝ X (paddingBaseCLM n d ξ) (Y (paddingBaseCLM n d ξ))) 0
  rw [fderiv_paddingBaseField Y ξ _ hY, fderiv_paddingBaseField X ξ _ hX,
    paddingBaseCLM_baseField, paddingBaseCLM_baseField]
  have hs (v w : Fin n → ℝ) :
      joinPoint v (0 : Fin d → ℝ) - joinPoint w 0 = joinPoint (v - w) 0 := by
    rw [← paddingJoinCLM_apply n d v 0, ← paddingJoinCLM_apply n d w 0,
      ← paddingJoinCLM_apply n d (v - w) 0, ← map_sub]
    congr 1
    ext <;> simp
  exact hs _ _

end RothschildStein.P1

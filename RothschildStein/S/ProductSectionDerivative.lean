-- Copyright (c) 2026 Scott Armstrong and Amélie Loher. All rights reserved.
-- Released under Apache 2.0 license as described in the file LICENSE.
module

public import Mathlib.Analysis.Calculus.ContDiff.Operations
public import Mathlib.Analysis.Normed.Operator.Prod

set_option autoImplicit false
set_option relaxedAutoImplicit false
set_option backward.isDefEq.respectTransparency false
@[expose] public section
noncomputable section
open Set Function
open scoped Topology ContDiff
namespace RothschildStein.S
variable {P G : Type*} [NormedAddCommGroup P] [NormedSpace ℝ P]
    [NormedAddCommGroup G] [NormedSpace ℝ G]

/-- The derivative of a first-variable section equals the
joint derivative applied to a first-variable direction (BB pp. 76–78). -/
theorem fderiv_productSection_first_apply {f : P × G → ℝ}
    (hf : ContDiff ℝ (⊤ : ℕ∞) f) (x : P) (y : G) (v : P) :
    fderiv ℝ (fun x => f (x,y)) x v = fderiv ℝ f (x,y) (v,0) := by
  let L : P →L[ℝ] P × G := (ContinuousLinearMap.id ℝ P).prod 0
  have ha : HasFDerivAt (fun x : P => (x,y)) L x := by
    simpa only [L,ContinuousLinearMap.prod_apply,ContinuousLinearMap.id_apply,
      zero_apply,Prod.mk_add_mk,add_zero,zero_add] using! L.hasFDerivAt.add_const (0,y)
  have H := (hf.differentiable (by simp)).differentiableAt.hasFDerivAt.comp x ha
  simp only [Function.comp_def] at H
  rw [H.fderiv]
  rfl

/-- The derivative of a second-variable section equals the
joint derivative applied to a second-variable direction (BB pp. 76–78). -/
theorem fderiv_productSection_second_apply {f : P × G → ℝ}
    (hf : ContDiff ℝ (⊤ : ℕ∞) f) (x : P) (y v : G) :
    fderiv ℝ (fun y => f (x,y)) y v = fderiv ℝ f (x,y) (0,v) := by
  let L : G →L[ℝ] P × G := (0 : G →L[ℝ] P).prod (ContinuousLinearMap.id ℝ G)
  have ha : HasFDerivAt (fun y : G => (x,y)) L y := by
    simpa only [L,ContinuousLinearMap.prod_apply,ContinuousLinearMap.id_apply,
      zero_apply,Prod.mk_add_mk,add_zero,zero_add] using! L.hasFDerivAt.add_const (x,0)
  have H := (hf.differentiable (by simp)).differentiableAt.hasFDerivAt.comp y ha
  simp only [Function.comp_def] at H
  rw [H.fderiv]
  rfl

end RothschildStein.S

-- Copyright (c) 2026 Scott Armstrong and Amélie Loher. All rights reserved.
-- Released under Apache 2.0 license as described in the file LICENSE.
module

public import RothschildStein.H1.LocalMaxSecondDerivative
public import Mathlib.Analysis.Calculus.Deriv.Mul
public import Mathlib.Analysis.Calculus.FDeriv.CompCLM

set_option autoImplicit false
set_option relaxedAutoImplicit false
set_option backward.isDefEq.respectTransparency false
@[expose] public section
noncomputable section
open Filter
open scoped Topology
namespace RothschildStein.H1
variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]

/-- Lemma 4.1: the Hessian at a C2 local maximum is nonpositive
on every diagonal direction (BB Thm 1.57, pp. 37–38). -/
theorem IsLocalMax.hessian_nonpos {f : E → ℝ} {x : E}
    (h : IsLocalMax f x) (hf : ContDiffAt ℝ 2 f x) (v : E) :
    fderiv ℝ (fderiv ℝ f) x v v ≤ 0 := by
  let l : ℝ → E := fun t => x + t • v
  have hl (t : ℝ) : HasDerivAt l v t := by
    have H := (hasDerivAt_const t x).add ((hasDerivAt_id t).smul_const v)
    have he : ((fun _ : ℝ => x) + fun s : ℝ => s • v) = l := by
      funext s
      rfl
    change HasDerivAt ((fun _ : ℝ => x) + fun s : ℝ => s • v) (0 + 1 • v) t at H
    rw [he] at H
    simpa only [zero_add, one_smul] using H
  have hl0 : l 0 = x := by simp [l]
  have hn : ∀ᶠ t in 𝓝 (0 : ℝ), ContDiffAt ℝ 2 f (l t) :=
    (hl 0).continuousAt.eventually (by simpa only [hl0] using hf.eventually (by norm_num))
  have he : deriv (f ∘ l) =ᶠ[𝓝 (0 : ℝ)] fun t => fderiv ℝ f (l t) v := by
    filter_upwards [hn] with t ht
    exact (ht.differentiableAt (by norm_num) |>.hasFDerivAt.comp_hasDerivAt t (hl t)).deriv
  have hdf := (hf.fderiv_right (m := 1) (by norm_num)).differentiableAt_one.hasFDerivAt
  have hd : HasDerivAt (fun t => fderiv ℝ f (l t) v)
      (fderiv ℝ (fderiv ℝ f) x v v) 0 := by
    have H := (hdf.comp_hasDerivAt_of_eq 0 (hl 0) hl0.symm).clm_apply (hasDerivAt_const 0 v)
    simpa only [ContinuousLinearMap.map_zero, add_zero, Function.comp_apply] using H
  have hm : IsLocalMax (f ∘ l) 0 := by
    apply IsLocalMax.comp_continuous
    · simpa only [hl0] using h
    · exact (hl 0).continuousAt
  have hc : ContinuousAt (f ∘ l) 0 := hf.continuousAt.comp_of_eq (hl 0).continuousAt hl0
  have H := IsLocalMax.second_deriv_nonpos hm hc
  rw [he.deriv_eq, hd.deriv] at H
  exact H

end RothschildStein.H1

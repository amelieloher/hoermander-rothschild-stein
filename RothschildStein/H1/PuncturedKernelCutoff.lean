-- Copyright (c) 2026 Scott Armstrong and Amélie Loher. All rights reserved.
-- Released under Apache 2.0 license as described in the file LICENSE.
module

public import RothschildStein.H1.FieldCutoffSupport
public import Mathlib.Analysis.Calculus.FDeriv.Mul

set_option autoImplicit false
set_option relaxedAutoImplicit false
@[expose] public section
noncomputable section
open Set Filter Topology
namespace RothschildStein.H1
variable {N : ℕ}

/-- Step 1: a cutoff vanishing near the origin turns a
punctured C¹ kernel into a globally C¹ function. -/
theorem contDiff_puncturedKernel_mul_cutoff
    {f θ : (Fin N → ℝ) → ℝ} (hf : ContDiffOn ℝ 1 f {(0 : Fin N → ℝ)}ᶜ)
    (hθ : ContDiff ℝ 1 θ) (he : θ =ᶠ[𝓝 (0 : Fin N → ℝ)] fun _ => 0) :
    ContDiff ℝ 1 (fun x => f x * θ x) := by
  apply contDiff_iff_contDiffAt.mpr
  intro x
  by_cases hx : x = 0
  · subst x
    have hz : (fun x => f x * θ x) =ᶠ[𝓝 (0 : Fin N → ℝ)] fun _ => 0 := by
      filter_upwards [he] with y hy
      rw [hy, mul_zero]
    exact (contDiffAt_const : ContDiffAt ℝ 1 (fun _ : Fin N → ℝ => (0 : ℝ)) 0).congr_of_eventuallyEq hz
  · exact (hf.contDiffAt (isOpen_compl_singleton.mem_nhds (by simpa using hx))).mul hθ.contDiffAt

/-- Step 1: the Leibniz rule for the regularized kernel,
including the origin, where the cutoff kills both terms. -/
theorem fieldDerivative_puncturedKernel_mul_cutoff
    (V : (Fin N → ℝ) → (Fin N → ℝ))
    {f θ : (Fin N → ℝ) → ℝ} (hf : ContDiffOn ℝ 1 f {(0 : Fin N → ℝ)}ᶜ)
    (hθ : ContDiff ℝ 1 θ) (he : θ =ᶠ[𝓝 (0 : Fin N → ℝ)] fun _ => 0) :
    fieldDerivative V (fun x => f x * θ x) =
      fun x => θ x * fieldDerivative V f x + f x * fieldDerivative V θ x := by
  funext x
  by_cases hx : x = 0
  · subst x
    have hz : (fun x => f x * θ x) =ᶠ[𝓝 (0 : Fin N → ℝ)] fun _ => 0 := by
      filter_upwards [he] with y hy
      rw [hy, mul_zero]
    have hd : fderiv ℝ θ 0 = 0 := by
      rw [he.fderiv_eq, fderiv_const_apply]
    have hp : fderiv ℝ (fun x => f x * θ x) 0 = 0 := by
      rw [hz.fderiv_eq, fderiv_const_apply]
    unfold fieldDerivative
    rw [hp, hd, he.eq_of_nhds]
    simp
  · have hdf : DifferentiableAt ℝ f x :=
      (hf.contDiffAt (isOpen_compl_singleton.mem_nhds (by simpa using hx))).differentiableAt (by norm_num)
    have hdθ := (hθ.differentiable (by norm_num)).differentiableAt (x := x)
    rw [S.fieldDerivative_mul V f θ x hdf hdθ]
    ring

end RothschildStein.H1

-- Copyright (c) 2026 Scott Armstrong and Amélie Loher. All rights reserved.
-- Released under Apache 2.0 license as described in the file LICENSE.
module
public import RothschildStein.L1.BlockDerivativeEquiv
public import Mathlib.Analysis.Calculus.InverseFunctionTheorem.ContDiff
public import Mathlib.Analysis.Normed.Module.FiniteDimension
@[expose] public section
set_option autoImplicit false
set_option relaxedAutoImplicit false
noncomputable section
open Filter
open scoped Topology
namespace RothschildStein.L1

/-- A differentiable right inverse has an injective derivative on
its equal-dimensional coordinate space. -/
theorem coordinateDerivative_injective_of_right_inverse {N : ℕ}
    (θ K : (Fin N → ℝ) → (Fin N → ℝ)) (x : Fin N → ℝ)
    (hθ : DifferentiableAt ℝ θ x) (hK : DifferentiableAt ℝ K (θ x))
    (hright : (K ∘ θ) =ᶠ[𝓝 x] (id : (Fin N → ℝ) → (Fin N → ℝ))) :
    Function.Injective (fderiv ℝ θ x) := by
  have hd := hK.hasFDerivAt.comp x hθ.hasFDerivAt
  have he := (hd.congr_of_eventuallyEq hright.symm).unique (hasFDerivAt_id x)
  intro v w hvw
  have hh := congrArg (fderiv ℝ K (θ x)) hvw
  change ((fderiv ℝ K (θ x)).comp (fderiv ℝ θ x)) v =
    ((fderiv ℝ K (θ x)).comp (fderiv ℝ θ x)) w at hh
  simpa only [he,ContinuousLinearMap.id_apply] using hh

/-- An injective derivative of a smooth square map constructs a local
smooth coordinate change by the inverse function theorem. -/
theorem exists_local_chart_of_injective_derivative {N : ℕ}
    (θ : (Fin N → ℝ) → (Fin N → ℝ)) (x : Fin N → ℝ)
    (hθ : ContDiffAt ℝ (⊤ : ℕ∞) θ x) (hi : Function.Injective (fderiv ℝ θ x)) :
    ∃ e : OpenPartialHomeomorph (Fin N → ℝ) (Fin N → ℝ),
      (e : (Fin N → ℝ) → (Fin N → ℝ)) = θ ∧ x ∈ e.source ∧
      ContDiffAt ℝ (⊤ : ℕ∞) e.symm (θ x) := by
  have hn : (↑(⊤ : ℕ∞) : WithTop ℕ∞) ≠ 0 := by simp
  let B := (LinearEquiv.ofInjectiveEndo (fderiv ℝ θ x).toLinearMap hi).toContinuousLinearEquiv
  have hD : HasFDerivAt θ (B : (Fin N → ℝ) →L[ℝ] (Fin N → ℝ)) x :=
    (hθ.differentiableAt hn).hasFDerivAt
  refine ⟨hθ.toOpenPartialHomeomorph θ hD hn,rfl,
    hθ.mem_toOpenPartialHomeomorph_source hD hn,?_⟩
  exact hθ.to_localInverse hD hn

end RothschildStein.L1

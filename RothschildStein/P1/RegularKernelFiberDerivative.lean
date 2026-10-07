-- Copyright (c) 2026 Scott Armstrong and Amélie Loher. All rights reserved.
-- Released under Apache 2.0 license as described in the file LICENSE.
module

public import RothschildStein.P1.RegularKernelOutputDerivative
public import RothschildStein.S.ClassicalWords

set_option autoImplicit false
set_option relaxedAutoImplicit false
@[expose] public section
noncomputable section
open Set
namespace RothschildStein.P1
variable {N : ℕ} {F : KernelFrame N}

/-- The joint output derivative equals the derivative of the actual
output fiber, with the input held fixed. -/
theorem regularKernel_output_fderiv_eq
    {r : (Fin N → ℝ) → (Fin N → ℝ) → ℝ}
    (hr : IsRegularKernel F 1 r) (ξ η v : Fin N → ℝ) :
    fderiv ℝ (fun z : (Fin N → ℝ) × (Fin N → ℝ) => r z.1 z.2)
      (ξ, η) (v, 0) = fderiv ℝ (fun x => r x η) ξ v := by
  have hd := (hr.1.differentiable (by simp) (ξ, η)).hasFDerivAt.comp ξ
    ((hasFDerivAt_id (𝕜 := ℝ) ξ).prodMk (hasFDerivAt_const (𝕜 := ℝ) η ξ))
  have he := congrArg (fun L : (Fin N → ℝ) →L[ℝ] ℝ => L v) hd.fderiv
  simpa only [Function.comp_def, id_eq, ContinuousLinearMap.comp_apply,
    ContinuousLinearMap.prod_apply, zero_apply, ContinuousLinearMap.id_apply] using he.symm

/-- The actual fiber derivative of a regular kernel is regular,
with one order of regularity consumed. -/
theorem IsRegularKernel.fieldDerivative_output {b : ℕ}
    {r : (Fin N → ℝ) → (Fin N → ℝ) → ℝ}
    (hr : IsRegularKernel F (b + 1) r)
    (Y : (Fin N → ℝ) → (Fin N → ℝ))
    (hY : ContDiffOn ℝ (⊤ : ℕ∞) Y (F.V : Set (Fin N → ℝ))) :
    IsRegularKernel F b (fun ξ η => fieldDerivative Y (fun x => r x η) ξ) := by
  have h1 : IsRegularKernel F 1 r := ⟨hr.1.of_le (by simp), hr.2⟩
  have he : (fun ξ η => fderiv ℝ
      (fun z : (Fin N → ℝ) × (Fin N → ℝ) => r z.1 z.2) (ξ, η) (Y ξ, 0)) =
      (fun ξ η => fieldDerivative Y (fun x => r x η) ξ) := by
    funext ξ η
    exact regularKernel_output_fderiv_eq h1 ξ η (Y ξ)
  rw [← he]
  exact hr.outputDerivative Y hY

end RothschildStein.P1

-- Copyright (c) 2026 Scott Armstrong and Amélie Loher. All rights reserved.
-- Released under Apache 2.0 license as described in the file LICENSE.
module

public import RothschildStein.P1.PrincipalModelKernel

@[expose] public section
set_option autoImplicit false
set_option relaxedAutoImplicit false
set_option backward.isDefEq.respectTransparency false
noncomputable section
open Set
namespace RothschildStein.P1
variable {N : ℕ}

/-- Differentiation in the model fiber is the
pure model-variable part of the joint kernel derivative, off its pole. -/
theorem kernelUncurry_fderiv_model
    (Ψ : (Fin N → ℝ) → (Fin N → ℝ) → (Fin N → ℝ) → ℝ)
    (hΨ : ContDiffOn ℝ 1 (kernelUncurry Ψ) {z | z.2.2 ≠ 0})
    (ξ η u v : Fin N → ℝ) (hu : u ≠ 0) :
    fderiv ℝ (kernelUncurry Ψ) (ξ, η, u) (0, 0, v) =
      fderiv ℝ (Ψ ξ η) u v := by
  have ho : IsOpen {z : (Fin N → ℝ) × (Fin N → ℝ) × (Fin N → ℝ) | z.2.2 ≠ 0} :=
    isOpen_ne_fun continuous_snd.snd continuous_const
  have hd := (hΨ.contDiffAt (ho.mem_nhds (show (ξ, η, u) ∈ {z | z.2.2 ≠ 0} from hu))).differentiableAt (by simp)
  have h := hd.hasFDerivAt.comp u
    ((hasFDerivAt_const (𝕜 := ℝ) ξ u).prodMk
      ((hasFDerivAt_const (𝕜 := ℝ) η u).prodMk (hasFDerivAt_id (𝕜 := ℝ) u)))
  have he := congrArg (fun L : (Fin N → ℝ) →L[ℝ] ℝ => L v) h.fderiv
  simpa only [Function.comp_def, id_eq, kernelUncurry, ContinuousLinearMap.comp_apply,
    ContinuousLinearMap.prod_apply, zero_apply, ContinuousLinearMap.id_apply] using he.symm

/-- Differentiation in the endpoint pair is
the corresponding part of the joint kernel derivative, holding u fixed. -/
theorem kernelUncurry_fderiv_parameter
    (Ψ : (Fin N → ℝ) → (Fin N → ℝ) → (Fin N → ℝ) → ℝ)
    (hΨ : ContDiffOn ℝ 1 (kernelUncurry Ψ) {z | z.2.2 ≠ 0})
    (ξ η u v₁ v₂ : Fin N → ℝ) (hu : u ≠ 0) :
    fderiv ℝ (kernelUncurry Ψ) (ξ, η, u) (v₁, v₂, 0) =
      fderiv ℝ (fun p : (Fin N → ℝ) × (Fin N → ℝ) => Ψ p.1 p.2 u)
        (ξ, η) (v₁, v₂) := by
  have ho : IsOpen {z : (Fin N → ℝ) × (Fin N → ℝ) × (Fin N → ℝ) | z.2.2 ≠ 0} :=
    isOpen_ne_fun continuous_snd.snd continuous_const
  have hd := (hΨ.contDiffAt (ho.mem_nhds (show (ξ, η, u) ∈ {z | z.2.2 ≠ 0} from hu))).differentiableAt (by simp)
  have h := hd.hasFDerivAt.comp (ξ, η)
    ((hasFDerivAt_fst (𝕜 := ℝ) (p := (ξ, η))).prodMk
      ((hasFDerivAt_snd (𝕜 := ℝ) (p := (ξ, η))).prodMk (hasFDerivAt_const (𝕜 := ℝ) u (ξ, η))))
  have he := congrArg (fun L : ((Fin N → ℝ) × (Fin N → ℝ)) →L[ℝ] ℝ => L (v₁, v₂)) h.fderiv
  simpa only [Function.comp_def, id_eq, kernelUncurry, ContinuousLinearMap.comp_apply,
    ContinuousLinearMap.prod_apply, zero_apply, ContinuousLinearMap.coe_fst',
    ContinuousLinearMap.coe_snd'] using he.symm

end RothschildStein.P1

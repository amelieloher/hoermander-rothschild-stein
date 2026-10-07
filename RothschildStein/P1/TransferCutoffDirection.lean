-- Copyright (c) 2026 Scott Armstrong and Amélie Loher. All rights reserved.
-- Released under Apache 2.0 license as described in the file LICENSE.
module

public import RothschildStein.P1.TransferKernelChainRule

@[expose] public section
set_option autoImplicit false
set_option relaxedAutoImplicit false
set_option backward.isDefEq.respectTransparency false
noncomputable section
open Set MvPolynomial
open scoped BigOperators
namespace RothschildStein.P1.LiftedChart
variable {n k m : ℕ} {w : Fin k → ℕ+} {s : ℕ} {Ω : Set (Fin n → ℝ)}
  {hΩ : IsOpen Ω} {X : Fin k → (Fin n → ℝ) → (Fin n → ℝ)} {x₀ : Fin n → ℝ}
  (C : LiftedChart w s Ω hΩ X x₀ m)

/-- Transferring the model cutoff as a whole
cancels all homogeneous cutoff derivatives. The remaining cutoff
flux is exactly the full weighted transfer remainder (BB p. 557,
critical endpoint proof in Theorem 11.24). -/
theorem transfer_cutoff_direction (i : Fin k) (φ : (Fin (n+m) → ℝ) → ℝ)
    (hφ : ContDiff ℝ (⊤ : ℕ∞) φ) {ξ η : Fin (n+m) → ℝ}
    (hξ : ξ ∈ C.U) (hη : η ∈ C.U) :
    fieldDerivative (C.Xl i) (fun ζ => φ (C.Θ η ζ)) ξ +
      ∑ j, eval (C.Θ η ξ) (C.generatorTransferCoefficient i j) *
        fieldDerivative (wordBracket C.Xl (C.B j)) (fun ζ => φ (C.Θ ζ ξ)) η =
      fieldDerivative (C.generatorTransferRemainder i ξ η) φ (C.Θ η ξ) := by
  classical
  have hφd := (hφ.differentiable (by simp) (C.Θ η ξ)).hasFDerivAt
  have hθo := ((C.theta_contDiffOn_right hη).contDiffAt
    (C.isOpen_U.mem_nhds hξ)).differentiableAt (by simp)
  have hθi : DifferentiableAt ℝ (fun ζ => C.Θ ζ ξ) η :=
    ((C.theta_smooth.comp (contDiffOn_id.prodMk contDiffOn_const)
      (fun _ hζ => ⟨hζ, hξ⟩)).contDiffAt (C.isOpen_U.mem_nhds hη)).differentiableAt (by simp)
  have ho := hφd.comp ξ hθo.hasFDerivAt
  have hi := hφd.comp η hθi.hasFDerivAt
  change HasFDerivAt (fun ζ => φ (C.Θ η ζ)) _ ξ at ho
  change HasFDerivAt (fun ζ => φ (C.Θ ζ ξ)) _ η at hi
  simp only [fieldDerivative, ho.fderiv, hi.fderiv, ContinuousLinearMap.comp_apply]
  have ht := C.generator_model_transfer i φ hξ hη
  simp only [fieldDerivative] at ht
  linarith

end RothschildStein.P1.LiftedChart

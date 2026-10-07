-- Copyright (c) 2026 Scott Armstrong and Amélie Loher. All rights reserved.
-- Released under Apache 2.0 license as described in the file LICENSE.
module

public import RothschildStein.P1.RegularTransferErrorKernel
public import RothschildStein.P1.PrincipalTransferIdentity
public import RothschildStein.P1.KernelFiberDifferentiability

set_option autoImplicit false
set_option relaxedAutoImplicit false
set_option backward.isDefEq.respectTransparency false
@[expose] public section
noncomputable section
open Set Filter MvPolynomial
open scoped BigOperators Topology
namespace RothschildStein.P1.LiftedChart
variable {n k m : ℕ} {w : Fin k → ℕ+} {s : ℕ} {Ω : Set (Fin n → ℝ)}
  {hΩ : IsOpen Ω} {X : Fin k → (Fin n → ℝ) → (Fin n → ℝ)} {x₀ : Fin n → ℝ}
  (C : LiftedChart w s Ω hΩ X x₀ m) (F : KernelFrame (n+m))

/-- The actual transfer error is linear in
smooth kernel fibers. Differentiability is required only at the
current off-diagonal endpoints (BB Theorem 11.24, pp. 555–558). -/
theorem regularTransferErrorKernel_add (i : Fin k)
    (f g : (Fin (n+m) → ℝ) → (Fin (n+m) → ℝ) → ℝ)
    {ξ η : Fin (n+m) → ℝ} (hξ : ξ ∈ C.U) (hη : η ∈ C.U)
    (hΘ : F.Θ = C.Θ)
    (hfo : DifferentiableAt ℝ (fun ζ => f ζ η) ξ)
    (hgo : DifferentiableAt ℝ (fun ζ => g ζ η) ξ)
    (hfi : DifferentiableAt ℝ (f ξ) η) (hgi : DifferentiableAt ℝ (g ξ) η) :
    C.regularTransferErrorKernel F i (fun x y => f x y + g x y) ξ η =
      C.regularTransferErrorKernel F i f ξ η + C.regularTransferErrorKernel F i g ξ η := by
  classical
  have hp (j : Fin (n+m)) : DifferentiableAt ℝ
      (fun ζ => eval (F.Θ ζ ξ) (C.generatorTransferCoefficient i j)) η := by
    rw [hΘ]
    have hd := ((C.transferEndpointCoefficient_smooth i j).contDiffAt
      ((C.isOpen_U.prod C.isOpen_U).mem_nhds (show (ξ, η) ∈ C.U ×ˢ C.U from ⟨hξ, hη⟩))).differentiableAt (by simp)
    exact hd.comp η (differentiableAt_const ξ |>.prodMk differentiableAt_id)
  have he (j : Fin (n+m)) :
      fieldDerivative (wordBracket C.Xl (C.B j))
        (fun ζ => C.generatorTransferKernel F i j (fun x y => f x y + g x y) ξ ζ) η =
      fieldDerivative (wordBracket C.Xl (C.B j))
        (fun ζ => C.generatorTransferKernel F i j f ξ ζ) η +
      fieldDerivative (wordBracket C.Xl (C.B j))
        (fun ζ => C.generatorTransferKernel F i j g ξ ζ) η := by
    have hfun : (fun ζ => C.generatorTransferKernel F i j (fun x y => f x y + g x y) ξ ζ) =
        (fun ζ => C.generatorTransferKernel F i j f ξ ζ + C.generatorTransferKernel F i j g ξ ζ) := by
      funext ζ; simp only [generatorTransferKernel, mul_add]
    rw [hfun]
    exact congrArg (fun L : (Fin (n+m) → ℝ) →L[ℝ] ℝ => L (wordBracket C.Xl (C.B j) η))
      (fderiv_fun_add ((hp j).mul hfi) ((hp j).mul hgi))
  unfold regularTransferErrorKernel
  simp_rw [he]
  simp only [fieldDerivative, fderiv_fun_add hfo hgo, add_apply, generatorTransferKernel,
    mul_add, Finset.sum_add_distrib]
  ring

/-- The transfer error depends only on the
actual output and input germs, so off-diagonal type decompositions
can be differentiated without fixing a decomposition globally. -/
theorem regularTransferErrorKernel_congr_germs (i : Fin k)
    (f g : (Fin (n+m) → ℝ) → (Fin (n+m) → ℝ) → ℝ) (ξ η : Fin (n+m) → ℝ)
    (ho : (fun ζ => f ζ η) =ᶠ[𝓝 ξ] fun ζ => g ζ η)
    (hi : f ξ =ᶠ[𝓝 η] g ξ) :
    C.regularTransferErrorKernel F i f ξ η = C.regularTransferErrorKernel F i g ξ η := by
  have hp (j : Fin (n+m)) :
      (fun ζ => C.generatorTransferKernel F i j f ξ ζ) =ᶠ[𝓝 η]
        (fun ζ => C.generatorTransferKernel F i j g ξ ζ) := by
    filter_upwards [hi] with ζ hζ
    simp only [generatorTransferKernel, hζ]
  have hsum : (∑ j, fieldDerivative (wordBracket C.Xl (C.B j))
      (fun ζ => C.generatorTransferKernel F i j f ξ ζ) η) =
      ∑ j, fieldDerivative (wordBracket C.Xl (C.B j))
        (fun ζ => C.generatorTransferKernel F i j g ξ ζ) η := by
    apply Finset.sum_congr rfl
    intro j _
    exact congrArg (fun L : (Fin (n+m) → ℝ) →L[ℝ] ℝ => L (wordBracket C.Xl (C.B j) η))
      (hp j).fderiv_eq
  unfold regularTransferErrorKernel
  rw [hsum]
  simp only [fieldDerivative, ho.fderiv_eq, generatorTransferKernel, hi.self_of_nhds]

end RothschildStein.P1.LiftedChart

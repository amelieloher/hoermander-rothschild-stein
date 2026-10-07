-- Copyright (c) 2026 Scott Armstrong and Amélie Loher. All rights reserved.
-- Released under Apache 2.0 license as described in the file LICENSE.
module

public import RothschildStein.P1.RegularTransferWeakIdentity
public import RothschildStein.P1.PrincipalTransferRegularization
public import RothschildStein.P1.TransferWholeCutoff
public import RothschildStein.P1.PrincipalTransferIdentity

set_option autoImplicit false
set_option relaxedAutoImplicit false
set_option backward.isDefEq.respectTransparency false
@[expose] public section
noncomputable section
open Set Filter MeasureTheory
open scoped Topology BigOperators
namespace RothschildStein.P1.LiftedChart
variable {n k m : ℕ} {w : Fin k → ℕ+} {s : ℕ} {Ω : Set (Fin n → ℝ)}
  {hΩ : IsOpen Ω} {X : Fin k → (Fin n → ℝ) → (Fin n → ℝ)} {x₀ : Fin n → ℝ}
  (C : LiftedChart w s Ω hΩ X x₀ m) (F : KernelFrame (n+m))

/-- The principal error construction equals
the generic transfer error off the diagonal (BB pp. 555–556). -/
theorem principalTransferErrorKernel_eq_generic (hF : C.IsLiftedFrame F)
    (t : PrincipalTerm F) (i : Fin k) {ξ η : Fin (n+m) → ℝ}
    (hξ : ξ ∈ C.U) (hη : η ∈ C.U) (hne : ξ ≠ η) :
    C.principalTransferErrorKernel F hF t i ξ η =
      C.regularTransferErrorKernel F i t.kernel ξ η := by
  rw [C.principalTransferErrorKernel_eq F hF t i hξ hη hne]
  simp only [regularTransferErrorKernel]

/-- At every finite cutoff, the principal
kernel has an actual weak transfer identity by regular-kernel integration
by parts. The cutoff acts on the entire original kernel (BB p. 557). -/
theorem principalCutoff_action_hasWeakWordDeriv (hF : C.IsLiftedFrame F)
    (t : PrincipalTerm F) (i : Fin k)
    (χ : (Fin (n+m) → ℝ) → ℝ) (hχ : ContDiff ℝ (⊤ : ℕ∞) χ)
    (heχ : χ =ᶠ[𝓝 (0 : Fin (n+m) → ℝ)] fun _ => 0)
    (φ : TestFunction F.V ℝ (⊤ : ℕ∞)) :
    hasWeakWordDeriv C.Xl F.V [i]
      (fun ξ => ∫ η, (χ (F.Θ η ξ) * t.kernel ξ η) * φ η)
      (fun ξ => (∑ j, ∫ η,
        C.generatorTransferKernel F i j (fun x y => χ (F.Θ y x) * t.kernel x y) ξ η *
          fieldDerivative (wordBracket C.Xl (C.B j)) φ η) +
        ∫ η, C.regularTransferErrorKernel F i
          (fun x y => χ (F.Θ y x) * t.kernel x y) ξ η * φ η) :=
  C.regularTransfer_action_hasWeakWordDeriv F hF
    (C.isRegularKernel_principalTransferCutoff F hF.Θ_eq
      (subset_closure.trans hF.closure_subset) t (hF.pole_smooth t.star) χ hχ heχ 1) i φ

/-- The finite principal cutoff error is
its cutoff times the typed principal error plus the full transfer
remainder flux. All homogeneous cutoff derivatives cancel (BB p. 557). -/
theorem principalCutoff_transfer_error_eq (hF : C.IsLiftedFrame F)
    (t : PrincipalTerm F) (i : Fin k)
    (χ : (Fin (n+m) → ℝ) → ℝ) (hχ : ContDiff ℝ (⊤ : ℕ∞) χ)
    {ξ η : Fin (n+m) → ℝ} (hξ : ξ ∈ C.U) (hη : η ∈ C.U) (hne : ξ ≠ η) :
    C.regularTransferErrorKernel F i (fun x y => χ (F.Θ y x) * t.kernel x y) ξ η =
      χ (C.Θ η ξ) * C.principalTransferErrorKernel F hF t i ξ η +
        t.kernel ξ η * fieldDerivative (C.generatorTransferRemainder i ξ η) χ (C.Θ η ξ) := by
  rw [hF.Θ_eq]
  rw [C.regularTransferErrorKernel_wholeCutoff F hF.Θ_eq i χ hχ t.kernel hξ hη]
  · rw [C.principalTransferErrorKernel_eq_generic F hF t i hξ hη hne]
  · exact C.principalKernel_differentiableAt hF t hξ hη hne
  · exact C.transferPrincipal_input_differentiableAt F hF t hξ hη hne

end RothschildStein.P1.LiftedChart

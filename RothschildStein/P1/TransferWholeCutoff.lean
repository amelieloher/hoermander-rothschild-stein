-- Copyright (c) 2026 Scott Armstrong and Amélie Loher. All rights reserved.
-- Released under Apache 2.0 license as described in the file LICENSE.
module

public import RothschildStein.P1.TransferErrorOperator
public import RothschildStein.P1.TransferCutoffDirection

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
  (C : LiftedChart w s Ω hΩ X x₀ m) (F : KernelFrame (n+m))

/-- Differentiating and transferring the
whole model-cutoff kernel produces its cutoff times the canonical
error plus exactly the full weighted-remainder cutoff flux. No
homogeneous boundary term survives (BB p. 557, Theorem 11.24). -/
theorem regularTransferErrorKernel_wholeCutoff (hΘ : F.Θ = C.Θ) (i : Fin k)
    (φ : (Fin (n+m) → ℝ) → ℝ) (hφ : ContDiff ℝ (⊤ : ℕ∞) φ)
    (κ : (Fin (n+m) → ℝ) → (Fin (n+m) → ℝ) → ℝ)
    {ξ η : Fin (n+m) → ℝ} (hξ : ξ ∈ C.U) (hη : η ∈ C.U)
    (hκo : DifferentiableAt ℝ (fun ζ => κ ζ η) ξ)
    (hκi : DifferentiableAt ℝ (κ ξ) η) :
    C.regularTransferErrorKernel F i (fun x y => φ (C.Θ y x) * κ x y) ξ η =
      φ (C.Θ η ξ) * C.regularTransferErrorKernel F i κ ξ η +
      κ ξ η * fieldDerivative (C.generatorTransferRemainder i ξ η) φ (C.Θ η ξ) := by
  classical
  have hθo := ((C.theta_contDiffOn_right hη).contDiffAt
    (C.isOpen_U.mem_nhds hξ)).differentiableAt (by simp)
  have hθi : DifferentiableAt ℝ (fun ζ => C.Θ ζ ξ) η :=
    ((C.theta_smooth.comp (contDiffOn_id.prodMk contDiffOn_const)
      (fun _ hζ => ⟨hζ, hξ⟩)).contDiffAt (C.isOpen_U.mem_nhds hη)).differentiableAt (by simp)
  have hφd := hφ.differentiable (by simp) (C.Θ η ξ)
  have hφo : DifferentiableAt ℝ (fun ζ => φ (C.Θ η ζ)) ξ := hφd.comp ξ hθo
  have hp (j : Fin (n+m)) : DifferentiableAt ℝ
      (fun ζ => eval (F.Θ ζ ξ) (C.generatorTransferCoefficient i j)) η := by
    rw [hΘ]
    exact (G2.contDiff_eval _).differentiable (by simp) _ |>.comp η hθi
  have he (j : Fin (n+m)) :
      fieldDerivative (wordBracket C.Xl (C.B j))
        (fun ζ => C.generatorTransferKernel F i j (fun x y => φ (C.Θ y x) * κ x y) ξ ζ) η =
      fieldDerivative (wordBracket C.Xl (C.B j)) (fun ζ => φ (C.Θ ζ ξ)) η *
        C.generatorTransferKernel F i j κ ξ η +
      φ (C.Θ η ξ) * fieldDerivative (wordBracket C.Xl (C.B j))
        (fun ζ => C.generatorTransferKernel F i j κ ξ ζ) η := by
    have hfun : (fun ζ => C.generatorTransferKernel F i j (fun x y => φ (C.Θ y x) * κ x y) ξ ζ) =
        fun ζ => φ (C.Θ ζ ξ) * C.generatorTransferKernel F i j κ ξ ζ := by
      funext ζ; simp only [generatorTransferKernel]; ring
    rw [hfun]
    exact S.fieldDerivative_mul _ _ _ η (hφd.comp η hθi) ((hp j).mul hκi)
  have ht := C.transfer_cutoff_direction i φ hφ hξ hη
  have hs := congrArg (fun z : ℝ => κ ξ η * z) ht
  unfold regularTransferErrorKernel
  rw [S.fieldDerivative_mul _ _ _ ξ hφo hκo]
  simp_rw [he]
  simp only [generatorTransferKernel, hΘ, mul_add, Finset.sum_add_distrib,
    Finset.mul_sum] at hs ⊢
  ring_nf at hs ⊢
  have hcomm : (∑ j, κ ξ η * eval (C.Θ η ξ) (C.generatorTransferCoefficient i j) *
      fieldDerivative (wordBracket C.Xl (C.B j)) (fun ζ => φ (C.Θ ζ ξ)) η) =
      ∑ j, κ ξ η * fieldDerivative (wordBracket C.Xl (C.B j))
        (fun ζ => φ (C.Θ ζ ξ)) η * eval (C.Θ η ξ) (C.generatorTransferCoefficient i j) := by
    apply Finset.sum_congr rfl
    intro j _
    ring
  rw [hcomm] at hs
  linarith

end RothschildStein.P1.LiftedChart

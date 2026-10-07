-- Copyright (c) 2026 Scott Armstrong and Amélie Loher. All rights reserved.
-- Released under Apache 2.0 license as described in the file LICENSE.
module

public import RothschildStein.P1.TransferFluxIntegrability
public import RothschildStein.P1.InputModelRowIntegrability

set_option autoImplicit false
set_option relaxedAutoImplicit false
set_option backward.isDefEq.respectTransparency false
@[expose] public section
noncomputable section
open Set Filter MeasureTheory
namespace RothschildStein.P1.LiftedChart
variable {n k m : ℕ} {w : Fin k → ℕ+} {s : ℕ} {Ω : Set (Fin n → ℝ)}
  {hΩ : IsOpen Ω} {X : Fin k → (Fin n → ℝ) → (Fin n → ℝ)} {x₀ : Fin n → ℝ}
  {C : LiftedChart w s Ω hΩ X x₀ m}

/-- The actual full transfer cutoff flux
transports to the reflected model row with moving endpoints and Jacobian. -/
theorem integral_inputModel_transfer_flux {ξ : Fin (n+m) → ℝ} (hξ : ξ ∈ C.U)
    (i : Fin k)
    (Ψ : (Fin (n+m) → ℝ) → (Fin (n+m) → ℝ) → (Fin (n+m) → ℝ) → ℝ)
    (χ : (Fin (n+m) → ℝ) → ℝ) (ψ : TestFunction C.chartOpens ℝ (⊤ : ℕ∞)) :
    (∫ η, Ψ ξ η (C.Θ η ξ) *
      fieldDerivative (C.generatorTransferRemainder i ξ η) χ (C.Θ η ξ) * ψ η) =
      ∫ u, Ψ ξ ((C.e ξ).symm (-u)) u *
        fieldDerivative (fun v => C.generatorTransferRemainder i ξ ((C.e ξ).symm (-v)) v) χ u *
        C.reflectedTransport ξ ψ u := by
  let g := fun u => Ψ ξ ((C.e ξ).symm (-u)) u *
    fieldDerivative (C.generatorTransferRemainder i ξ ((C.e ξ).symm (-u))) χ u
  have hz : ∀ η, η ∉ C.U → Ψ ξ η (C.Θ η ξ) *
      fieldDerivative (C.generatorTransferRemainder i ξ η) χ (C.Θ η ξ) * ψ η = 0 := by
    intro η hη
    rw [image_eq_zero_of_notMem_tsupport (fun ht => hη (ψ.tsupport_subset ht)), mul_zero]
  rw [← setIntegral_eq_integral_of_forall_compl_eq_zero hz]
  have he : (∫ η in C.U, Ψ ξ η (C.Θ η ξ) *
      fieldDerivative (C.generatorTransferRemainder i ξ η) χ (C.Θ η ξ) * ψ η) =
      ∫ η in C.U, g (C.Θ η ξ) * ψ η := by
    apply setIntegral_congr_fun C.isOpen_U.measurableSet
    intro η hη
    have hinv : (C.e ξ).symm (-C.Θ η ξ) = η := by
      rw [C.theta_antisymm ξ hξ η hη, neg_neg]
      exact C.symm_theta hξ hη
    dsimp only [g]
    rw [hinv]
  rw [he, C.integral_input_theta_mul hξ g ψ]
  rfl

end RothschildStein.P1.LiftedChart

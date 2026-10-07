-- Copyright (c) 2026 Scott Armstrong and Amélie Loher. All rights reserved.
-- Released under Apache 2.0 license as described in the file LICENSE.
module

public import RothschildStein.P1.VariableCoordinateCutoffScaling
public import RothschildStein.P1.GeneratorTransferJets
public import RothschildStein.P1.KernelEstimatesWeightedTaylor
public import RothschildStein.P1.TransferInputParameterRange
public import RothschildStein.P1.TransferFluxIntegrability
public import RothschildStein.P1.PrincipalModelDerivative
public import RothschildStein.H1.FieldSubtractConstant

set_option autoImplicit false
set_option relaxedAutoImplicit false
set_option backward.isDefEq.respectTransparency false
@[expose] public section
noncomputable section
open Set Filter MeasureTheory
open scoped Topology
namespace RothschildStein.P1.LiftedChart
variable {n k m : ℕ} {w : Fin k → ℕ+} {s : ℕ} {Ω : Set (Fin n → ℝ)}
  {hΩ : IsOpen Ω} {X : Fin k → (Fin n → ℝ) → (Fin n → ℝ)} {x₀ : Fin n → ℝ}
  {C : LiftedChart w s Ω hΩ X x₀ m}

/-- The full reflected remainder flux is the
finite sum of its integrable coordinate fluxes, including every coordinate. -/
theorem integral_inputModel_transfer_fieldCutoff
    {ξ : Fin (n + m) → ℝ} (hξ : ξ ∈ C.U) (i : Fin k)
    (Ψ : (Fin (n + m) → ℝ) → (Fin (n + m) → ℝ) → (Fin (n + m) → ℝ) → ℝ)
    (hΨ : ContinuousOn (kernelUncurry Ψ) {z | z.2.2 ≠ 0})
    {θ : (Fin (n + m) → ℝ) → ℝ} (hθ : ContDiff ℝ (⊤ : ℕ∞) θ)
    (heθ : θ =ᶠ[𝓝 (0 : Fin (n + m) → ℝ)] fun _ => 1)
    (ε : ℝ) (ψ : TestFunction C.chartOpens ℝ (⊤ : ℕ∞)) :
    (∫ u, Ψ ξ ((C.e ξ).symm (-u)) u *
      fieldDerivative (fun v => C.generatorTransferRemainder i ξ ((C.e ξ).symm (-v)) v) (θ ∘ C.G.dilate ε⁻¹) u *
      C.reflectedTransport ξ ψ u) =
    ∑ j, ∫ u, Ψ ξ ((C.e ξ).symm (-u)) u * C.generatorTransferRemainder i ξ ((C.e ξ).symm (-u)) u j *
      fderiv ℝ (θ ∘ C.G.dilate ε⁻¹) u (Pi.single j 1) * C.reflectedTransport ξ ψ u := by
  classical
  have he : (fun u => Ψ ξ ((C.e ξ).symm (-u)) u *
      fieldDerivative (fun v => C.generatorTransferRemainder i ξ ((C.e ξ).symm (-v)) v) (θ ∘ C.G.dilate ε⁻¹) u *
      C.reflectedTransport ξ ψ u) = fun u => ∑ j,
        Ψ ξ ((C.e ξ).symm (-u)) u * C.generatorTransferRemainder i ξ ((C.e ξ).symm (-u)) u j *
          fderiv ℝ (θ ∘ C.G.dilate ε⁻¹) u (Pi.single j 1) * C.reflectedTransport ξ ψ u := by
    funext u
    rw [fieldDerivative_coordinate_sum, Finset.mul_sum, Finset.sum_mul]
    apply Finset.sum_congr rfl
    intro j _
    ring
  rw [he, integral_finsetSum _ (fun j _ =>
    C.integrable_inputModel_transfer_coordinateCutoff hξ i j Ψ hΨ hθ heθ ε ψ)]

/-- Every full transfer remainder cutoff row is integrable before taking its limit. -/
theorem integrable_inputModel_transfer_fieldCutoff
    {ξ : Fin (n + m) → ℝ} (hξ : ξ ∈ C.U) (i : Fin k)
    (Ψ : (Fin (n + m) → ℝ) → (Fin (n + m) → ℝ) → (Fin (n + m) → ℝ) → ℝ)
    (hΨ : ContinuousOn (kernelUncurry Ψ) {z | z.2.2 ≠ 0})
    {θ : (Fin (n + m) → ℝ) → ℝ} (hθ : ContDiff ℝ (⊤ : ℕ∞) θ)
    (heθ : θ =ᶠ[𝓝 (0 : Fin (n + m) → ℝ)] fun _ => 1)
    (ε : ℝ) (ψ : TestFunction C.chartOpens ℝ (⊤ : ℕ∞)) :
    Integrable (fun u => Ψ ξ ((C.e ξ).symm (-u)) u *
      fieldDerivative (fun v => C.generatorTransferRemainder i ξ ((C.e ξ).symm (-v)) v) (θ ∘ C.G.dilate ε⁻¹) u *
        C.reflectedTransport ξ ψ u) := by
  classical
  have hi := integrable_finsetSum Finset.univ (fun j _ =>
    C.integrable_inputModel_transfer_coordinateCutoff hξ i j Ψ hΨ hθ heθ ε ψ)
  apply hi.congr
  apply Eventually.of_forall
  intro u
  change (∑ j, Ψ ξ ((C.e ξ).symm (-u)) u * C.generatorTransferRemainder i ξ ((C.e ξ).symm (-u)) u j *
    fderiv ℝ (θ ∘ C.G.dilate ε⁻¹) u (Pi.single j 1) * C.reflectedTransport ξ ψ u) =
    Ψ ξ ((C.e ξ).symm (-u)) u *
      fieldDerivative (fun v => C.generatorTransferRemainder i ξ ((C.e ξ).symm (-v)) v) (θ ∘ C.G.dilate ε⁻¹) u *
      C.reflectedTransport ξ ψ u
  rw [fieldDerivative_coordinate_sum, Finset.mul_sum, Finset.sum_mul]
  apply Finset.sum_congr rfl
  intro j _
  ring

end RothschildStein.P1.LiftedChart

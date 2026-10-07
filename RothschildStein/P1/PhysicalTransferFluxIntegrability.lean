-- Copyright (c) 2026 Scott Armstrong and Amélie Loher. All rights reserved.
-- Released under Apache 2.0 license as described in the file LICENSE.
module

public import RothschildStein.P1.TransferRemainderFieldFlux
public import RothschildStein.P1.InputModelRowIntegrability

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

/-- The full exterior transfer flux is
integrable in physical input coordinates before splitting the finite
regularized error integral (BB Theorem 11.24, p. 557). -/
theorem integrable_physicalTransfer_exteriorFlux
    {ξ : Fin (n+m) → ℝ} (hξ : ξ ∈ C.U) (i : Fin k)
    (Ψ : (Fin (n+m) → ℝ) → (Fin (n+m) → ℝ) → (Fin (n+m) → ℝ) → ℝ)
    (hΨ : ContinuousOn (kernelUncurry Ψ) {z | z.2.2 ≠ 0})
    {θ : (Fin (n+m) → ℝ) → ℝ} (hθ : ContDiff ℝ (⊤ : ℕ∞) θ)
    (heθ : θ =ᶠ[𝓝 (0 : Fin (n+m) → ℝ)] fun _ => 1)
    (ε : ℝ) (ψ : TestFunction C.chartOpens ℝ (⊤ : ℕ∞)) :
    Integrable (fun η => Ψ ξ η (C.Θ η ξ) *
      fieldDerivative (C.generatorTransferRemainder i ξ η)
        ((fun v => 1 - θ v) ∘ C.G.dilate ε⁻¹) (C.Θ η ξ) * ψ η) := by
  let χ := (fun v => 1 - θ v) ∘ C.G.dilate ε⁻¹
  have hi := C.integrable_inputModel_transfer_fieldCutoff hξ i Ψ hΨ hθ heθ ε ψ
  have he : fieldDerivative
      (fun v => C.generatorTransferRemainder i ξ ((C.e ξ).symm (-v)) v) χ =
      fun u => -fieldDerivative
        (fun v => C.generatorTransferRemainder i ξ ((C.e ξ).symm (-v)) v)
        (θ ∘ C.G.dilate ε⁻¹) u :=
    H1.fieldDerivative_one_sub_C1 _
      ((hθ.comp (G2.contDiff_dilate C.G ε⁻¹)).of_le (by simp))
  have hm : Integrable (fun u => Ψ ξ ((C.e ξ).symm (-u)) u *
      fieldDerivative (C.generatorTransferRemainder i ξ ((C.e ξ).symm (-u))) χ u *
        C.reflectedTransport ξ ψ u) := by
    apply hi.neg.congr
    apply Filter.Eventually.of_forall
    intro u
    have hp := congrFun he u
    change fieldDerivative (C.generatorTransferRemainder i ξ ((C.e ξ).symm (-u))) χ u = _ at hp
    change -(Ψ ξ ((C.e ξ).symm (-u)) u *
      fieldDerivative (C.generatorTransferRemainder i ξ ((C.e ξ).symm (-u)))
        (θ ∘ C.G.dilate ε⁻¹) u * C.reflectedTransport ξ ψ u) =
      Ψ ξ ((C.e ξ).symm (-u)) u *
        fieldDerivative (C.generatorTransferRemainder i ξ ((C.e ξ).symm (-u))) χ u *
        C.reflectedTransport ξ ψ u
    rw [hp]
    simp only [fieldDerivative]
    ring
  have hlocal := C.integrable_inputRow_of_model hξ
    (fun ξ η u => Ψ ξ η u * fieldDerivative (C.generatorTransferRemainder i ξ η) χ u) ψ hm
  apply (integrableOn_iff_integrable_of_support_subset ?_).mp hlocal
  intro η hη
  by_contra hn
  exact hη (by
    change Ψ ξ η (C.Θ η ξ) * fieldDerivative (C.generatorTransferRemainder i ξ η) χ (C.Θ η ξ) * ψ η = 0
    rw [image_eq_zero_of_notMem_tsupport (fun hs => hn (ψ.tsupport_subset hs)), mul_zero])

end RothschildStein.P1.LiftedChart

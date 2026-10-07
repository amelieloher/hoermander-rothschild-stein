-- Copyright (c) 2026 Scott Armstrong and Amélie Loher. All rights reserved.
-- Released under Apache 2.0 license as described in the file LICENSE.
module

public import RothschildStein.P1.InputBoundaryTransport
public import RothschildStein.P1.InputRemainderFieldFlux
public import RothschildStein.P1.ReflectedModelGenerator

set_option autoImplicit false
set_option relaxedAutoImplicit false
set_option backward.isDefEq.respectTransparency false
@[expose] public section
noncomputable section
open Set Filter MeasureTheory
open scoped Topology
namespace RothschildStein.P1
variable {N : ℕ}

/-- The exterior cutoff derivative is integrable whenever its interior
counterpart is integrable, since the two rows are negatives. -/
theorem integrable_exteriorFieldCutoff
    (Y : (Fin N → ℝ) → (Fin N → ℝ))
    (f φ θ : (Fin N → ℝ) → ℝ) (hθ : ContDiff ℝ 1 θ)
    (hi : Integrable (fun u => f u * fieldDerivative Y θ u * φ u)) :
    Integrable (fun u => f u * fieldDerivative Y (fun v => 1 - θ v) u * φ u) := by
  rw [H1.fieldDerivative_one_sub_C1 Y hθ]
  exact hi.neg.congr (Eventually.of_forall (fun u => by
    change -(f u * fieldDerivative Y θ u * φ u) =
      f u * -fieldDerivative Y θ u * φ u
    ring))

namespace LiftedChart
variable {n k m : ℕ} {w : Fin k → ℕ+} {s : ℕ} {Ω : Set (Fin n → ℝ)}
  {hΩ : IsOpen Ω} {X : Fin k → (Fin n → ℝ) → (Fin n → ℝ)} {x₀ : Fin n → ℝ}
  {C : LiftedChart w s Ω hΩ X x₀ m}

/-- The transported boundary integral splits into
its genuinely integrable reflected generator and full remainder terms. -/
theorem integral_input_boundary_split
    {ξ : Fin (n + m) → ℝ} (hξ : ξ ∈ C.U) (i : Fin k)
    (Ψ : (Fin (n + m) → ℝ) → (Fin (n + m) → ℝ) → (Fin (n + m) → ℝ) → ℝ)
    (hΨ : ContinuousOn (kernelUncurry Ψ) {z | z.2.2 ≠ 0})
    {θ : (Fin (n + m) → ℝ) → ℝ} (hθ : ContDiff ℝ (⊤ : ℕ∞) θ)
    (heθ : θ =ᶠ[𝓝 (0 : Fin (n + m) → ℝ)] fun _ => 1)
    (ε : ℝ) (ψ : TestFunction C.chartOpens ℝ (⊤ : ℕ∞)) :
    (∫ η, -(fieldDerivative (C.Xl i)
      (fun ζ => 1 - θ (C.G.dilate ε⁻¹ (C.Θ ζ ξ))) η) * Ψ ξ η (C.Θ η ξ) * ψ η) =
    (∫ u, Ψ ξ ((C.e ξ).symm (-u)) u *
      fieldDerivative (fun v => C.Y i (-v)) ((fun v => 1 - θ v) ∘ C.G.dilate ε⁻¹) u *
        C.reflectedTransport ξ ψ u) +
    ∫ u, Ψ ξ ((C.e ξ).symm (-u)) u *
      fieldDerivative (fun v => C.R [i] ξ (-v)) ((fun v => 1 - θ v) ∘ C.G.dilate ε⁻¹) u *
        C.reflectedTransport ξ ψ u := by
  have hc : ContDiff ℝ 1 (θ ∘ C.G.dilate ε⁻¹) :=
    (hθ.comp (G2.contDiff_dilate C.G ε⁻¹)).of_le (by simp)
  have hY := integrable_exteriorFieldCutoff (fun v => C.Y i (-v))
    (fun u => Ψ ξ ((C.e ξ).symm (-u)) u) (C.reflectedTransport ξ ψ)
    (θ ∘ C.G.dilate ε⁻¹) hc
    (C.integrable_inputModel_fieldCutoff hξ Ψ hΨ _ (C.reflectedGenerator_contDiff i) hθ heθ ε ψ)
  have hR := integrable_exteriorFieldCutoff (fun v => C.R [i] ξ (-v))
    (fun u => Ψ ξ ((C.e ξ).symm (-u)) u) (C.reflectedTransport ξ ψ)
    (θ ∘ C.G.dilate ε⁻¹) hc
    (C.integrable_inputModel_remainder_fieldCutoff hξ i Ψ hΨ hθ heθ ε ψ)
  have he := C.integral_input_boundary_transport hξ i Ψ
    ((fun v => 1 - θ v) ∘ C.G.dilate ε⁻¹)
    (contDiff_const.sub (hθ.comp (G2.contDiff_dilate C.G ε⁻¹))) ψ
  simp only [Function.comp_def] at he
  rw [he]
  have hadd : (fun u => Ψ ξ ((C.e ξ).symm (-u)) u *
      (fieldDerivative (fun v => C.Y i (-v)) ((fun v => 1 - θ v) ∘ C.G.dilate ε⁻¹) u +
       fieldDerivative (fun v => C.R [i] ξ (-v)) ((fun v => 1 - θ v) ∘ C.G.dilate ε⁻¹) u) *
      C.reflectedTransport ξ ψ u) = fun u =>
    Ψ ξ ((C.e ξ).symm (-u)) u *
      fieldDerivative (fun v => C.Y i (-v)) ((fun v => 1 - θ v) ∘ C.G.dilate ε⁻¹) u * C.reflectedTransport ξ ψ u +
    Ψ ξ ((C.e ξ).symm (-u)) u *
      fieldDerivative (fun v => C.R [i] ξ (-v)) ((fun v => 1 - θ v) ∘ C.G.dilate ε⁻¹) u * C.reflectedTransport ξ ψ u := by
    funext u
    ring
  simp only [Function.comp_def] at hadd hY hR
  rw [hadd]
  exact integral_add hY hR

end LiftedChart
end RothschildStein.P1

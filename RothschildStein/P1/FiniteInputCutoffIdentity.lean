-- Copyright (c) 2026 Scott Armstrong and Amélie Loher. All rights reserved.
-- Released under Apache 2.0 license as described in the file LICENSE.
module

public import RothschildStein.P1.InputFiberCutoffRegularity
public import RothschildStein.P1.SmoothInputIntegrationByParts
public import RothschildStein.P1.ModelHypotheses
public import RothschildStein.S.Transposes

set_option autoImplicit false
set_option relaxedAutoImplicit false
set_option backward.isDefEq.respectTransparency false
@[expose] public section
noncomputable section
open Set MeasureTheory Filter
open scoped Topology
namespace RothschildStein.P1.LiftedChart
variable {n k m : ℕ} {w : Fin k → ℕ+} {s : ℕ} {Ω : Set (Fin n → ℝ)}
  {hΩ : IsOpen Ω} {X : Fin k → (Fin n → ℝ) → (Fin n → ℝ)} {x₀ : Fin n → ℝ}
  {C : LiftedChart w s Ω hΩ X x₀ m} {F : KernelFrame (n + m)}

/-- Exact finite-cutoff input integration by
parts for the actual type kernel. The differentiated cutoff and the
divergence are both retained. No limit identity is a premise. -/
theorem isTypeKernel_finite_inputCutoff_identity {lam : ℕ}
    (hF : C.IsLiftedFrame F) {κ : (Fin (n + m) → ℝ) → (Fin (n + m) → ℝ) → ℝ}
    (hκ : IsTypeKernel F lam κ) {ξ : Fin (n + m) → ℝ}
    (hξ : ξ ∈ (F.V : Set (Fin (n + m) → ℝ))) (i : Fin k)
    {θ : (Fin (n + m) → ℝ) → ℝ} (hθ : ContDiff ℝ (⊤ : ℕ∞) θ)
    (heθ : θ =ᶠ[𝓝 (0 : Fin (n + m) → ℝ)] fun _ => 1)
    (ε : ℝ) (φ : TestFunction F.V ℝ (⊤ : ℕ∞)) :
    (∫ η, ((1 - θ (C.G.dilate ε⁻¹ (C.Θ η ξ))) * κ ξ η) * fieldDerivative (C.Xl i) φ η) =
      ∫ η, ((1 - θ (C.G.dilate ε⁻¹ (C.Θ η ξ))) *
        (-fieldDerivative (C.Xl i) (fun ζ => κ ξ ζ) η -
          κ ξ η * Hormander.Interface.euclideanDivergence (C.Xl i) η) -
        fieldDerivative (C.Xl i) (fun ζ => 1 - θ (C.G.dilate ε⁻¹ (C.Θ ζ ξ))) η * κ ξ η) * φ η := by
  let rsFiniteInputCutoffFinNonempty : Nonempty (Fin (n + m)) :=
    ⟨⟨0, C.G.dimension_pos⟩⟩
  let χ := fun η => 1 - θ (C.G.dilate ε⁻¹ (C.Θ η ξ))
  have hVU : (F.V : Set (Fin (n + m) → ℝ)) ⊆ C.U :=
    subset_closure.trans hF.closure_subset
  have hY : ContDiffOn ℝ (⊤ : ℕ∞) (C.Xl i) (F.V : Set (Fin (n + m) → ℝ)) :=
    (C.lift_smooth i).mono (hVU.trans C.U_subset_O)
  have hΘ : ContDiffOn ℝ (⊤ : ℕ∞) (fun η => C.Θ η ξ)
      (F.V : Set (Fin (n + m) → ℝ)) :=
    C.theta_smooth.comp (contDiffOn_id.prodMk contDiffOn_const)
      (fun η hη => ⟨hVU hη, hVU hξ⟩)
  have hχ : ContDiffOn ℝ (⊤ : ℕ∞) χ (F.V : Set (Fin (n + m) → ℝ)) :=
    contDiffOn_const.sub ((hθ.comp (G2.contDiff_dilate C.G ε⁻¹)).comp_contDiffOn hΘ)
  have hg := C.isTypeKernel_contDiffOn_inputCutoff hF hκ hξ hθ heθ ε
  have hibp := smoothInput_integral_integrationByParts F.V (C.Xl i) hY
    (fun η => χ η * κ ξ η) hg φ
  rw [hibp]
  apply integral_congr_ae
  filter_upwards [volume.ae_ne ξ] with η hηξ
  by_cases hη : η ∈ (F.V : Set (Fin (n + m) → ℝ))
  · have hκd : DifferentiableAt ℝ (fun ζ => κ ξ ζ) η :=
      ((C.isTypeKernel_contDiffOn_input hF hκ (hVU hξ)).contDiffAt
        ((F.V.isOpen.sdiff isClosed_singleton).mem_nhds ⟨hη, hηξ⟩)).differentiableAt (by simp)
    have hχd := (hχ.contDiffAt (F.V.isOpen.mem_nhds hη)).differentiableAt (by simp)
    rw [S.fieldDerivative_mul (C.Xl i) χ (fun ζ => κ ξ ζ) η hχd hκd]
    change (-(_ * _ + _ * _) - _ * _) * _ = _
    ring
  · simp only [φ.zero_on_compl hη, Pi.zero_apply, mul_zero]

end RothschildStein.P1.LiftedChart

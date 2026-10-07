-- Copyright (c) 2026 Scott Armstrong and Amélie Loher. All rights reserved.
-- Released under Apache 2.0 license as described in the file LICENSE.
module

public import RothschildStein.P1.FiniteInputCutoffIdentity
public import RothschildStein.P1.TypeKernelInputTranspose

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
  {C : LiftedChart w s Ω hΩ X x₀ m} {F : KernelFrame (n + m)}

/-- Every finite smooth-cutoff row is genuinely
integrable on an interior test, independently of diagonal kernel values. -/
theorem isTypeKernel_integrable_inputCutoff {lam : ℕ}
    (hF : C.IsLiftedFrame F) {κ : (Fin (n + m) → ℝ) → (Fin (n + m) → ℝ) → ℝ}
    (hκ : IsTypeKernel F lam κ) {ξ : Fin (n + m) → ℝ}
    (hξ : ξ ∈ (F.V : Set (Fin (n + m) → ℝ)))
    {θ : (Fin (n + m) → ℝ) → ℝ} (hθ : ContDiff ℝ (⊤ : ℕ∞) θ)
    (heθ : θ =ᶠ[𝓝 (0 : Fin (n + m) → ℝ)] fun _ => 1)
    (ε : ℝ) (φ : TestFunction F.V ℝ (⊤ : ℕ∞)) :
    Integrable (fun η => ((1 - θ (C.G.dilate ε⁻¹ (C.Θ η ξ))) * κ ξ η) * φ η) :=
  S.integrable_mul_test F.V
    ((C.isTypeKernel_contDiffOn_inputCutoff hF hκ hξ hθ heθ ε).continuousOn.locallyIntegrableOn
      (μ := volume) F.V.isOpen.measurableSet) φ

/-- The exact finite-cutoff identity uses the
already classified formal-adjoint kernel, with its boundary flux retained. -/
theorem isTypeKernel_finite_inputCutoff_adjoint_identity {lam : ℕ}
    (hF : C.IsLiftedFrame F) {κ : (Fin (n + m) → ℝ) → (Fin (n + m) → ℝ) → ℝ}
    (hκ : IsTypeKernel F lam κ) {ξ : Fin (n + m) → ℝ}
    (hξ : ξ ∈ (F.V : Set (Fin (n + m) → ℝ))) (i : Fin k)
    {θ : (Fin (n + m) → ℝ) → ℝ} (hθ : ContDiff ℝ (⊤ : ℕ∞) θ)
    (heθ : θ =ᶠ[𝓝 (0 : Fin (n + m) → ℝ)] fun _ => 1)
    (ε : ℝ) (φ : TestFunction F.V ℝ (⊤ : ℕ∞)) :
    (∫ η, ((1 - θ (C.G.dilate ε⁻¹ (C.Θ η ξ))) * κ ξ η) * fieldDerivative (C.Xl i) φ η) =
      ∫ η, ((1 - θ (C.G.dilate ε⁻¹ (C.Θ η ξ))) *
        cutoffInputTranspose F (C.Xl i) κ ξ η -
        fieldDerivative (C.Xl i) (fun ζ => 1 - θ (C.G.dilate ε⁻¹ (C.Θ ζ ξ))) η * κ ξ η) * φ η := by
  let rsFiniteInputAdjointFinNonempty : Nonempty (Fin (n + m)) :=
    ⟨⟨0, C.G.dimension_pos⟩⟩
  rw [C.isTypeKernel_finite_inputCutoff_identity hF hκ hξ i hθ heθ ε φ]
  apply integral_congr_ae
  filter_upwards [volume.ae_ne ξ] with η hηξ
  by_cases hη : η ∈ (F.V : Set (Fin (n + m) → ℝ))
  · rw [cutoffInputTranspose_apply (C.Xl i) κ hξ hη hηξ.symm]
  · simp only [φ.zero_on_compl hη, Pi.zero_apply, mul_zero]

end RothschildStein.P1.LiftedChart

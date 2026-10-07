-- Copyright (c) 2026 Scott Armstrong and Amélie Loher. All rights reserved.
-- Released under Apache 2.0 license as described in the file LICENSE.
module

public import RothschildStein.P1.InputFiberCutoffRegularity
public import RothschildStein.P1.SmoothInputIntegrationByParts
public import RothschildStein.H1.FieldCutoffSupport

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

/-- An amplitude continuous on V and zero near
its pole makes every actual type-kernel test row integrable. -/
theorem isTypeKernel_integrable_inputPlateauMultiplier {lam : ℕ}
    (hF : C.IsLiftedFrame F) {κ : (Fin (n + m) → ℝ) → (Fin (n + m) → ℝ) → ℝ}
    (hκ : IsTypeKernel F lam κ) {ξ : Fin (n + m) → ℝ}
    (hξ : ξ ∈ (F.V : Set (Fin (n + m) → ℝ)))
    (A : (Fin (n + m) → ℝ) → ℝ)
    (hA : ContinuousOn A (F.V : Set (Fin (n + m) → ℝ)))
    (h0A : A =ᶠ[𝓝 ξ] fun _ => 0) (φ : TestFunction F.V ℝ (⊤ : ℕ∞)) :
    Integrable (fun η => (A η * κ ξ η) * φ η) := by
  have hκs := (C.isTypeKernel_contDiffOn_input hF hκ
    (hF.closure_subset (subset_closure hξ))).continuousOn
  have hc : ContinuousOn (fun η => A η * κ ξ η) (F.V : Set (Fin (n + m) → ℝ)) := by
    intro η hη
    apply ContinuousAt.continuousWithinAt
    by_cases he : η = ξ
    · subst η
      exact (continuousAt_const : ContinuousAt
        (fun _ : Fin (n + m) → ℝ => (0 : ℝ)) ξ).congr_of_eventuallyEq
        (h0A.mono (fun ζ hζ => by
          change A ζ * κ ξ ζ = 0
          change A ζ = 0 at hζ
          rw [hζ, zero_mul]))
    · exact (hA.continuousAt (F.V.isOpen.mem_nhds hη)).mul
        (hκs.continuousAt ((F.V.isOpen.sdiff isClosed_singleton).mem_nhds ⟨hη, he⟩))
  exact S.integrable_mul_test F.V
    (hc.locallyIntegrableOn (μ := volume) F.V.isOpen.measurableSet) φ

/-- The finite original-chart boundary row is
integrable independently of the arbitrary diagonal value of the kernel. -/
theorem isTypeKernel_integrable_inputBoundary {lam : ℕ}
    (hF : C.IsLiftedFrame F) {κ : (Fin (n + m) → ℝ) → (Fin (n + m) → ℝ) → ℝ}
    (hκ : IsTypeKernel F lam κ) {ξ : Fin (n + m) → ℝ}
    (hξ : ξ ∈ (F.V : Set (Fin (n + m) → ℝ))) (i : Fin k)
    {θ : (Fin (n + m) → ℝ) → ℝ} (hθ : ContDiff ℝ (⊤ : ℕ∞) θ)
    (heθ : θ =ᶠ[𝓝 (0 : Fin (n + m) → ℝ)] fun _ => 1)
    (ε : ℝ) (φ : TestFunction F.V ℝ (⊤ : ℕ∞)) :
    Integrable (fun η => -(fieldDerivative (C.Xl i)
      (fun ζ => 1 - θ (C.G.dilate ε⁻¹ (C.Θ ζ ξ))) η) * κ ξ η * φ η) := by
  have hVU : (F.V : Set (Fin (n + m) → ℝ)) ⊆ C.U :=
    subset_closure.trans hF.closure_subset
  have hY := (C.lift_smooth i).mono (hVU.trans C.U_subset_O)
  have hΘ : ContDiffOn ℝ (⊤ : ℕ∞) (fun η => C.Θ η ξ)
      (F.V : Set (Fin (n + m) → ℝ)) :=
    C.theta_smooth.comp (contDiffOn_id.prodMk contDiffOn_const) (fun η hη => ⟨hVU hη, hVU hξ⟩)
  let χ := fun η => 1 - θ (C.G.dilate ε⁻¹ (C.Θ η ξ))
  have hχ : ContDiffOn ℝ (⊤ : ℕ∞) χ (F.V : Set (Fin (n + m) → ℝ)) :=
    contDiffOn_const.sub ((hθ.comp (G2.contDiff_dilate C.G ε⁻¹)).comp_contDiffOn hΘ)
  have hχ1 : ContDiffOn ℝ 1 χ (F.V : Set (Fin (n + m) → ℝ)) := hχ.of_le (by simp)
  have hc : ContinuousOn (fieldDerivative (C.Xl i) χ) (F.V : Set (Fin (n + m) → ℝ)) :=
    (hχ1.continuousOn_fderiv_of_isOpen
      F.V.isOpen (by rfl)).clm_apply hY.continuousOn
  have ht := ((G2.contDiff_dilate C.G ε⁻¹).comp_contDiffOn hΘ).continuousOn.continuousAt
    (F.V.isOpen.mem_nhds hξ)
  have hz : C.G.dilate ε⁻¹ (C.Θ ξ ξ) = 0 := by
    rw [(C.chart ξ (hVU hξ)).2.2.2.2, G2.dilate_zero]
  have hlim := ht.tendsto
  simp only [Function.comp_apply] at hlim
  rw [hz] at hlim
  have hone := heθ.comp_tendsto hlim
  have hzero : χ =ᶠ[𝓝 ξ] fun _ => 0 := by
    filter_upwards [hone] with η hη
    simp only [Function.comp_apply] at hη
    change 1 - θ (C.G.dilate ε⁻¹ (C.Θ η ξ)) = 0
    rw [hη, sub_self]
  have hD := H1.fieldDerivative_eventuallyEq (C.Xl i) hzero
  have h0 : (fun η => -fieldDerivative (C.Xl i) χ η) =ᶠ[𝓝 ξ] fun _ => 0 := by
    filter_upwards [hD] with η hη
    rw [hη]
    simp only [fieldDerivative, fderiv_const_apply, zero_apply, neg_zero]
  exact C.isTypeKernel_integrable_inputPlateauMultiplier hF hκ hξ _ hc.neg h0 φ

end RothschildStein.P1.LiftedChart

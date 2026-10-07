-- Copyright (c) 2026 Scott Armstrong and Amélie Loher. All rights reserved.
-- Released under Apache 2.0 license as described in the file LICENSE.
module

public import RothschildStein.P1.ReflectedModelTest
public import RothschildStein.H1.FieldCutoffSupport
public import RothschildStein.G2.FieldHomogeneity

set_option autoImplicit false
set_option relaxedAutoImplicit false
set_option backward.isDefEq.respectTransparency false
@[expose] public section
noncomputable section
open Set Filter MeasureTheory
open scoped Topology
namespace RothschildStein.P1
variable {N : ℕ}

/-- The cutoff plateau persists under every fixed dilation. -/
theorem cutoff_dilate_eventually_one (G : HomogeneousGroup N)
    {θ : (Fin N → ℝ) → ℝ} (heθ : θ =ᶠ[𝓝 (0 : Fin N → ℝ)] fun _ => 1) (ε : ℝ) :
    θ ∘ G.dilate ε⁻¹ =ᶠ[𝓝 (0 : Fin N → ℝ)] fun _ => 1 := by
  have ht : Tendsto (G.dilate ε⁻¹) (𝓝 (0 : Fin N → ℝ)) (𝓝 0) := by
    simpa only [G2.dilate_zero] using (G2.continuous_dilate G ε⁻¹).tendsto (0 : Fin N → ℝ)
  simpa only [Function.comp_def] using heθ.comp_tendsto ht

namespace LiftedChart
variable {n k m : ℕ} {w : Fin k → ℕ+} {s : ℕ} {Ω : Set (Fin n → ℝ)}
  {hΩ : IsOpen Ω} {X : Fin k → (Fin n → ℝ) → (Fin n → ℝ)} {x₀ : Fin n → ℝ}
  {C : LiftedChart w s Ω hΩ X x₀ m}

/-- Finite integrability of the actual moving
family generator cutoff term is proved on the reflected chart target. -/
theorem integrable_inputModel_fieldCutoff {ξ : Fin (n + m) → ℝ} (hξ : ξ ∈ C.U)
    (Ψ : (Fin (n + m) → ℝ) → (Fin (n + m) → ℝ) → (Fin (n + m) → ℝ) → ℝ)
    (hΨ : ContinuousOn (kernelUncurry Ψ) {z | z.2.2 ≠ 0})
    (Y : (Fin (n + m) → ℝ) → (Fin (n + m) → ℝ)) (hY : ContDiff ℝ (⊤ : ℕ∞) Y)
    {θ : (Fin (n + m) → ℝ) → ℝ} (hθ : ContDiff ℝ (⊤ : ℕ∞) θ)
    (heθ : θ =ᶠ[𝓝 (0 : Fin (n + m) → ℝ)] fun _ => 1)
    (ε : ℝ) (ψ : TestFunction C.chartOpens ℝ (⊤ : ℕ∞)) :
    Integrable (fun u => Ψ ξ ((C.e ξ).symm (-u)) u *
      fieldDerivative Y (θ ∘ C.G.dilate ε⁻¹) u * C.reflectedTransport ξ ψ u) :=
  C.integrable_inputModel_cutoffProduct hξ Ψ hΨ _
    (H1.smooth_fieldDerivative Y hY _ (hθ.comp (G2.contDiff_dilate C.G ε⁻¹))).continuous.continuousOn
    (H1.fieldDerivative_cutoff_eventually_zero Y (cutoff_dilate_eventually_one C.G heθ ε)) ψ

/-- Every actual remainder coordinate cutoff
term is integrable before any finite sum or limit is taken. -/
theorem integrable_inputModel_remainder_coordinateCutoff
    {ξ : Fin (n + m) → ℝ} (hξ : ξ ∈ C.U) (i : Fin k) (j : Fin (n + m))
    (Ψ : (Fin (n + m) → ℝ) → (Fin (n + m) → ℝ) → (Fin (n + m) → ℝ) → ℝ)
    (hΨ : ContinuousOn (kernelUncurry Ψ) {z | z.2.2 ≠ 0})
    {θ : (Fin (n + m) → ℝ) → ℝ} (hθ : ContDiff ℝ (⊤ : ℕ∞) θ)
    (heθ : θ =ᶠ[𝓝 (0 : Fin (n + m) → ℝ)] fun _ => 1)
    (ε : ℝ) (ψ : TestFunction C.chartOpens ℝ (⊤ : ℕ∞)) :
    Integrable (fun u => Ψ ξ ((C.e ξ).symm (-u)) u * C.R [i] ξ (-u) j *
      fderiv ℝ (θ ∘ C.G.dilate ε⁻¹) u (Pi.single j 1) * C.reflectedTransport ξ ψ u) := by
  let E := fun _ : Fin (n + m) → ℝ => (Pi.single j 1 : Fin (n + m) → ℝ)
  have hR : ContinuousOn (fun u => C.R [i] ξ (-u) j)
      (C.reflectedModelOpens ξ : Set (Fin (n + m) → ℝ)) :=
    (continuous_apply j).comp_continuousOn
      ((C.remainder_smooth [i]).continuousOn.comp
        ((continuousOn_const (c := ξ)).prodMk continuousOn_id.neg) (fun _ hu => ⟨hξ, hu⟩))
  have hD : ContDiff ℝ (⊤ : ℕ∞) (fieldDerivative E (θ ∘ C.G.dilate ε⁻¹)) :=
    H1.smooth_fieldDerivative E contDiff_const _ (hθ.comp (G2.contDiff_dilate C.G ε⁻¹))
  have h0D := H1.fieldDerivative_cutoff_eventually_zero E (cutoff_dilate_eventually_one C.G heθ ε)
  have hi := C.integrable_inputModel_cutoffProduct hξ Ψ hΨ
    (fun u => C.R [i] ξ (-u) j * fieldDerivative E (θ ∘ C.G.dilate ε⁻¹) u)
    (hR.mul hD.continuous.continuousOn)
    (h0D.mono (fun u hu => by change _ * _ = 0; rw [hu, mul_zero])) ψ
  simpa only [mul_assoc, E, fieldDerivative] using hi

end LiftedChart
end RothschildStein.P1

-- Copyright (c) 2026 Scott Armstrong and Amélie Loher. All rights reserved.
-- Released under Apache 2.0 license as described in the file LICENSE.
module

public import RothschildStein.P1.InputModelCutoffIntegrability
public import RothschildStein.P1.GeneratorTransferRemainder

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
  {C : LiftedChart w s Ω hΩ X x₀ m}

/-- The full transfer remainder is continuous
on the reflected chart, including its moving input endpoint (BB p. 557). -/
theorem continuousOn_reflectedTransferRemainder
    {ξ : Fin (n+m) → ℝ} (hξ : ξ ∈ C.U) (i : Fin k) :
    ContinuousOn (fun u => C.generatorTransferRemainder i ξ ((C.e ξ).symm (-u)) u)
      (C.reflectedModelOpens ξ : Set (Fin (n+m) → ℝ)) := by
  classical
  have hI : ContinuousOn (fun u => (C.e ξ).symm (-u))
      (C.reflectedModelOpens ξ : Set (Fin (n+m) → ℝ)) :=
    (C.contDiffOn_symm hξ).continuousOn.comp continuousOn_id.neg (fun _ hu => hu)
  have hmap : MapsTo (fun u => ((C.e ξ).symm (-u), u))
      (C.reflectedModelOpens ξ : Set (Fin (n+m) → ℝ)) C.T := by
    intro u hu
    have hη : (C.e ξ).symm (-u) ∈ C.U := by
      rw [← C.e_source hξ]
      exact (C.e ξ).mapsTo_symm hu
    have he : C.Θ ξ ((C.e ξ).symm (-u)) = -u := by
      rw [← C.e_apply hξ hη]
      exact (C.e ξ).right_inv hu
    have ht : C.Θ ((C.e ξ).symm (-u)) ξ = u := by
      have ha := C.theta_antisymm ξ hξ _ hη
      rw [he, neg_neg] at ha
      exact ha
    change _ ∈ C.U ∧ u ∈ (C.e ((C.e ξ).symm (-u))).target
    have htarget := C.theta_mem_target hη hξ
    rw [ht] at htarget
    exact ⟨hη, htarget⟩
  have ho := (C.remainder_smooth [i]).continuousOn.comp (hI.prodMk continuousOn_id) hmap
  have hr (j : Fin (n+m)) : ContinuousOn (fun u => C.R (C.B j) ξ (-u))
      (C.reflectedModelOpens ξ : Set (Fin (n+m) → ℝ)) :=
    (C.remainder_smooth (C.B j)).continuousOn.comp
      (continuousOn_const.prodMk continuousOn_id.neg) (fun _ hu => ⟨hξ, hu⟩)
  exact ho.sub (continuousOn_finsetSum Finset.univ (fun j _ =>
    (G2.contDiff_eval (C.generatorTransferCoefficient i j)).continuous.continuousOn.smul (hr j)))

/-- Each complete remainder coordinate flux
is integrable before summing coordinates or taking the pole limit. -/
theorem integrable_inputModel_transfer_coordinateCutoff
    {ξ : Fin (n+m) → ℝ} (hξ : ξ ∈ C.U) (i : Fin k) (j : Fin (n+m))
    (Ψ : (Fin (n+m) → ℝ) → (Fin (n+m) → ℝ) → (Fin (n+m) → ℝ) → ℝ)
    (hΨ : ContinuousOn (kernelUncurry Ψ) {z | z.2.2 ≠ 0})
    {θ : (Fin (n+m) → ℝ) → ℝ} (hθ : ContDiff ℝ (⊤ : ℕ∞) θ)
    (heθ : θ =ᶠ[𝓝 (0 : Fin (n+m) → ℝ)] fun _ => 1)
    (ε : ℝ) (ψ : TestFunction C.chartOpens ℝ (⊤ : ℕ∞)) :
    Integrable (fun u => Ψ ξ ((C.e ξ).symm (-u)) u *
      C.generatorTransferRemainder i ξ ((C.e ξ).symm (-u)) u j *
      fderiv ℝ (θ ∘ C.G.dilate ε⁻¹) u (Pi.single j 1) * C.reflectedTransport ξ ψ u) := by
  let E := fun _ : Fin (n+m) → ℝ => (Pi.single j 1 : Fin (n+m) → ℝ)
  have hR := (continuous_apply j).comp_continuousOn
    (C.continuousOn_reflectedTransferRemainder hξ i)
  have hD : ContDiff ℝ (⊤ : ℕ∞) (fieldDerivative E (θ ∘ C.G.dilate ε⁻¹)) :=
    H1.smooth_fieldDerivative E contDiff_const _ (hθ.comp (G2.contDiff_dilate C.G ε⁻¹))
  have h0D := H1.fieldDerivative_cutoff_eventually_zero E (cutoff_dilate_eventually_one C.G heθ ε)
  have hi := C.integrable_inputModel_cutoffProduct hξ Ψ hΨ
    (fun u => C.generatorTransferRemainder i ξ ((C.e ξ).symm (-u)) u j *
      fieldDerivative E (θ ∘ C.G.dilate ε⁻¹) u)
    (hR.mul hD.continuous.continuousOn)
    (h0D.mono (fun u hu => by change _ * _ = 0; rw [hu, mul_zero])) ψ
  simpa only [mul_assoc, E, fieldDerivative] using hi

end RothschildStein.P1.LiftedChart

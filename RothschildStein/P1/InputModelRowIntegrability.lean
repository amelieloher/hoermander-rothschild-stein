-- Copyright (c) 2026 Scott Armstrong and Amélie Loher. All rights reserved.
-- Released under Apache 2.0 license as described in the file LICENSE.
module

public import RothschildStein.P1.ReflectedChartTransport

set_option autoImplicit false
set_option relaxedAutoImplicit false
set_option backward.isDefEq.respectTransparency false
@[expose] public section
noncomputable section
open Set MeasureTheory
namespace RothschildStein.P1.LiftedChart
variable {n k m : ℕ} {w : Fin k → ℕ+} {s : ℕ} {Ω : Set (Fin n → ℝ)}
  {hΩ : IsOpen Ω} {X : Fin k → (Fin n → ℝ) → (Fin n → ℝ)} {x₀ : Fin n → ℝ}
  {C : LiftedChart w s Ω hΩ X x₀ m}

/-- Integrable physical chart rows give
integrable reflected moving-endpoint model rows, with their full density. -/
theorem integrable_inputModel_of_row {ξ : Fin (n+m) → ℝ} (hξ : ξ ∈ C.U)
    (Ψ : (Fin (n+m) → ℝ) → (Fin (n+m) → ℝ) → (Fin (n+m) → ℝ) → ℝ)
    (ψ : (Fin (n+m) → ℝ) → ℝ)
    (hi : IntegrableOn (fun η => Ψ ξ η (C.Θ η ξ) * ψ η) C.U) :
    Integrable (fun u => Ψ ξ ((C.e ξ).symm (-u)) u * C.reflectedTransport ξ ψ u) := by
  let g := fun u => Ψ ξ ((C.e ξ).symm (-u)) u
  have hs : IntegrableOn (fun η => g (-C.Θ ξ η) * ψ η) C.U := by
    apply hi.congr_fun _ C.isOpen_U.measurableSet
    intro η hη
    have hinv : (C.e ξ).symm (-C.Θ η ξ) = η := by
      rw [C.theta_antisymm ξ hξ η hη, neg_neg]
      exact C.symm_theta hξ hη
    dsimp only [g]
    rw [C.theta_antisymm η hη ξ hξ, neg_neg, hinv]
    simp only [neg_neg]
  have hw := (C.integrableOn_comp_theta_mul_iff hξ (fun u => g (-u)) ψ).mp hs
  have hn := (Measure.measurePreserving_neg volume).integrable_comp_of_integrable hw
  simpa only [Function.comp_def, neg_neg, g, reflectedTransport] using hn

/-- Reflected model row integrability also
returns physical row integrability on the actual chart domain. -/
theorem integrable_inputRow_of_model {ξ : Fin (n+m) → ℝ} (hξ : ξ ∈ C.U)
    (Ψ : (Fin (n+m) → ℝ) → (Fin (n+m) → ℝ) → (Fin (n+m) → ℝ) → ℝ)
    (ψ : (Fin (n+m) → ℝ) → ℝ)
    (hi : Integrable (fun u => Ψ ξ ((C.e ξ).symm (-u)) u * C.reflectedTransport ξ ψ u)) :
    IntegrableOn (fun η => Ψ ξ η (C.Θ η ξ) * ψ η) C.U := by
  let g := fun u => Ψ ξ ((C.e ξ).symm (-u)) u
  have hn := (Measure.measurePreserving_neg volume).integrable_comp_of_integrable hi
  have hw : Integrable (fun u => g (-u) * C.modelTransport ξ ψ u) := by
    simpa only [Function.comp_def, neg_neg, g, reflectedTransport] using hn
  have hs := (C.integrableOn_comp_theta_mul_iff hξ (fun u => g (-u)) ψ).mpr hw
  apply hs.congr_fun _ C.isOpen_U.measurableSet
  intro η hη
  have hinv : (C.e ξ).symm (-C.Θ η ξ) = η := by
    rw [C.theta_antisymm ξ hξ η hη, neg_neg]
    exact C.symm_theta hξ hη
  dsimp only [g]
  rw [C.theta_antisymm η hη ξ hξ, neg_neg, hinv]
  simp only [neg_neg]

end RothschildStein.P1.LiftedChart

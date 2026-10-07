-- Copyright (c) 2026 Scott Armstrong and Amélie Loher. All rights reserved.
-- Released under Apache 2.0 license as described in the file LICENSE.
module

public import RothschildStein.P1.IntegrableModelMultiplier
public import RothschildStein.P1.InputModelRowIntegrability

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

/-- Whole smooth cutoff errors equal their
actual reflected model integrals, including moving input amplitudes. -/
theorem inputFamily_modelCutoff_sub_integral
    {ξ : Fin (n+m) → ℝ} (hξ : ξ ∈ C.U)
    (Ψ : (Fin (n+m) → ℝ) → (Fin (n+m) → ℝ) → (Fin (n+m) → ℝ) → ℝ)
    (ψ : TestFunction C.chartOpens ℝ (⊤ : ℕ∞))
    (hi : Integrable (fun η => Ψ ξ η (C.Θ η ξ) * ψ η))
    (χ : (Fin (n+m) → ℝ) → ℝ) (hχ : Continuous χ)
    {B : ℝ} (hb : ∀ u, ‖χ u‖ ≤ B) :
    (∫ η, (1 - χ (C.Θ η ξ)) * (Ψ ξ η (C.Θ η ξ) * ψ η)) -
      (∫ η, Ψ ξ η (C.Θ η ξ) * ψ η) =
      -(∫ u, χ u * (Ψ ξ ((C.e ξ).symm (-u)) u * C.reflectedTransport ξ ψ u)) := by
  have hz : ∀ η, η ∉ C.U → Ψ ξ η (C.Θ η ξ) * ψ η = 0 := by
    intro η hη
    rw [image_eq_zero_of_notMem_tsupport (fun ht => hη (ψ.tsupport_subset ht)), mul_zero]
  have hic := C.integrable_modelMultiplier hξ hi hz χ hχ hb
  have he : (fun η => (1 - χ (C.Θ η ξ)) * (Ψ ξ η (C.Θ η ξ) * ψ η)) =
      fun η => Ψ ξ η (C.Θ η ξ) * ψ η - χ (C.Θ η ξ) * (Ψ ξ η (C.Θ η ξ) * ψ η) := by
    funext η; ring
  rw [he, integral_sub hi hic]
  have htrans : (∫ η, χ (C.Θ η ξ) * (Ψ ξ η (C.Θ η ξ) * ψ η)) =
      ∫ u, χ u * (Ψ ξ ((C.e ξ).symm (-u)) u * C.reflectedTransport ξ ψ u) := by
    let g := fun u => χ u * Ψ ξ ((C.e ξ).symm (-u)) u
    have hs : (∫ η, χ (C.Θ η ξ) * (Ψ ξ η (C.Θ η ξ) * ψ η)) =
        ∫ η in C.U, g (C.Θ η ξ) * ψ η := by
      rw [← setIntegral_eq_integral_of_forall_compl_eq_zero (fun η hη => by rw [hz η hη, mul_zero])]
      apply setIntegral_congr_fun C.isOpen_U.measurableSet
      intro η hη
      have hinv : (C.e ξ).symm (-C.Θ η ξ) = η := by
        rw [C.theta_antisymm ξ hξ η hη, neg_neg]
        exact C.symm_theta hξ hη
      dsimp only [g]
      rw [hinv]
      ring
    rw [hs, C.integral_input_theta_mul hξ g ψ]
    apply integral_congr_ae
    exact Filter.Eventually.of_forall (fun u => by dsimp only [g]; ring)
  rw [htrans]
  ring

end RothschildStein.P1.LiftedChart

-- Copyright (c) 2026 Scott Armstrong and Amélie Loher. All rights reserved.
-- Released under Apache 2.0 license as described in the file LICENSE.
module

public import RothschildStein.P1.InputChartCutoffDerivative
public import RothschildStein.P1.ReflectedModelTest

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

/-- Exact input boundary transport with the full
reflected generator and remainder, before splitting any integral. -/
theorem integral_input_boundary_transport
    {ξ : Fin (n + m) → ℝ} (hξ : ξ ∈ C.U) (i : Fin k)
    (Ψ : (Fin (n + m) → ℝ) → (Fin (n + m) → ℝ) → (Fin (n + m) → ℝ) → ℝ)
    (χ : (Fin (n + m) → ℝ) → ℝ) (hχ : ContDiff ℝ (⊤ : ℕ∞) χ)
    (ψ : TestFunction C.chartOpens ℝ (⊤ : ℕ∞)) :
    (∫ η, -(fieldDerivative (C.Xl i) (fun ζ => χ (C.Θ ζ ξ)) η) *
      Ψ ξ η (C.Θ η ξ) * ψ η) =
    ∫ u, Ψ ξ ((C.e ξ).symm (-u)) u *
      (fieldDerivative (fun v => C.Y i (-v)) χ u +
        fieldDerivative (fun v => C.R [i] ξ (-v)) χ u) *
      C.reflectedTransport ξ ψ u := by
  let g := fun u => Ψ ξ ((C.e ξ).symm (-u)) u *
    (fieldDerivative (fun v => C.Y i (-v)) χ u +
      fieldDerivative (fun v => C.R [i] ξ (-v)) χ u)
  have he : (∫ η, -(fieldDerivative (C.Xl i) (fun ζ => χ (C.Θ ζ ξ)) η) *
      Ψ ξ η (C.Θ η ξ) * ψ η) =
      ∫ η in C.U, -(fieldDerivative (C.Xl i) (fun ζ => χ (C.Θ ζ ξ)) η) *
        Ψ ξ η (C.Θ η ξ) * ψ η :=
    (setIntegral_eq_integral_of_forall_compl_eq_zero (fun η hη => by
      rw [image_eq_zero_of_notMem_tsupport (fun ht => hη (ψ.tsupport_subset ht)), mul_zero])).symm
  rw [he, ← C.integral_input_theta_mul hξ g ψ]
  apply setIntegral_congr_fun C.isOpen_U.measurableSet
  intro η hη
  have hi : (C.e ξ).symm (-C.Θ η ξ) = η := by
    rw [C.theta_antisymm ξ hξ η hη, neg_neg]
    exact C.symm_theta hξ hη
  change -(fieldDerivative (C.Xl i) (fun ζ => χ (C.Θ ζ ξ)) η) *
    Ψ ξ η (C.Θ η ξ) * ψ η = g (C.Θ η ξ) * ψ η
  rw [C.inputChart_fieldDerivative_comp i hξ hη χ hχ]
  dsimp only [g]
  rw [hi]
  ring

end RothschildStein.P1.LiftedChart

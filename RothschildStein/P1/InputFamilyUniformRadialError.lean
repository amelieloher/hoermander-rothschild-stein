-- Copyright (c) 2026 Scott Armstrong and Amélie Loher. All rights reserved.
-- Released under Apache 2.0 license as described in the file LICENSE.
module

public import RothschildStein.P1.InputFamilyRadialDifference
public import RothschildStein.P1.RadialAbsoluteErrorBound
public import RothschildStein.G2.FieldHomogeneity

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

/-- An absolute model small-ball bound
controls the actual whole radial truncation error uniformly in centers. -/
theorem inputFamily_uniform_radialError_of_absoluteSmallBall
    {ν : (Fin (n+m) → ℝ) → ℝ} (hν : C.G.IsHomogeneousGauge ν)
    (Ψ : (Fin (n+m) → ℝ) → (Fin (n+m) → ℝ) → (Fin (n+m) → ℝ) → ℝ)
    (ψ : TestFunction C.chartOpens ℝ (⊤ : ℕ∞))
    {L : Set (Fin (n+m) → ℝ)} (hLU : L ⊆ C.U)
    (hi : ∀ ξ ∈ L, Integrable (fun η => Ψ ξ η (C.Θ η ξ) * ψ η))
    {r A : ℝ}
    (hb : ∀ ξ ∈ L, ∀ δ : ℝ, 0 < δ → δ ≤ r →
      ‖∫ u in {u | ν u ≤ δ}, ‖Ψ ξ ((C.e ξ).symm (-u)) u * C.reflectedTransport ξ ψ u‖‖ ≤ A * δ) :
    ∀ ξ ∈ L, ∀ ε : ℝ, 0 < ε → 2 * ε ≤ r →
      ‖(∫ η, (1 - radialCutoffProfile (ν (C.G.dilate ε⁻¹ (C.Θ η ξ)))) *
        (Ψ ξ η (C.Θ η ξ) * ψ η)) - (∫ η, Ψ ξ η (C.Θ η ξ) * ψ η)‖ ≤ (2 * A) * ε := by
  intro ξ hξ ε hε hεr
  rw [C.inputFamily_modelCutoff_sub_integral (hLU hξ) Ψ ψ (hi ξ hξ)
    (fun u => radialCutoffProfile (ν (C.G.dilate ε⁻¹ u)))
    (radialCutoffProfile_contDiff.continuous.comp (hν.1.comp (G2.continuous_dilate C.G ε⁻¹)))
    (fun u => radialCutoffProfile_norm_le _), norm_neg]
  have hm := C.integrable_inputModel_of_row (hLU hξ) Ψ ψ (hi ξ hξ).integrableOn
  have hnonneg : 0 ≤ ∫ u in {u | ν u ≤ 2 * ε},
      ‖Ψ ξ ((C.e ξ).symm (-u)) u * C.reflectedTransport ξ ψ u‖ :=
    integral_nonneg (fun _ => norm_nonneg _)
  calc
    _ ≤ ∫ u in {u | ν u ≤ 2 * ε},
      ‖Ψ ξ ((C.e ξ).symm (-u)) u * C.reflectedTransport ξ ψ u‖ :=
      norm_radialCutoff_integral_le C.G hν hm hε
    _ = ‖∫ u in {u | ν u ≤ 2 * ε},
      ‖Ψ ξ ((C.e ξ).symm (-u)) u * C.reflectedTransport ξ ψ u‖‖ :=
      (Real.norm_of_nonneg hnonneg).symm
    _ ≤ A * (2 * ε) := hb ξ hξ (2 * ε) (by positivity) hεr
    _ = _ := by ring

end RothschildStein.P1.LiftedChart

-- Copyright (c) 2026 Scott Armstrong and Amélie Loher. All rights reserved.
-- Released under Apache 2.0 license as described in the file LICENSE.
module

public import RothschildStein.P1.SharpInputChartTransport
public import RothschildStein.P1.AmbientTruncationLocalization

set_option autoImplicit false
set_option relaxedAutoImplicit false
@[expose] public section
noncomputable section
open Set MeasureTheory
namespace RothschildStein.P1.LiftedChart
variable {n k m : ℕ} {w : Fin k → ℕ+} {s : ℕ} {Ω : Set (Fin n → ℝ)}
  {hΩ : IsOpen Ω} {X : Fin k → (Fin n → ℝ) → (Fin n → ℝ)} {x₀ : Fin n → ℝ}
  {C : LiftedChart w s Ω hΩ X x₀ m}

/-- The ambient truncation of a kernel row with fixed input point equals its transported model
truncation; no global regularity of the chart map is required. -/
theorem integral_sharp_inputChart_ambient {ξ : Fin (n + m) → ℝ} (hξ : ξ ∈ C.U)
    (ν g : (Fin (n + m) → ℝ) → ℝ) (hν : Continuous ν) (ε : ℝ)
    (ψ : TestFunction C.chartOpens ℝ (⊤ : ℕ∞)) :
    (∫ η in {η | ε < ν (C.Θ η ξ)}, g (C.Θ η ξ) * ψ η) =
      ∫ u in {u | ε < ν u}, g u * C.reflectedTransport ξ ψ u := by
  have hz : ∀ η, η ∉ C.U → g (C.Θ η ξ) * ψ η = 0 := by
    intro η hη
    rw [image_eq_zero_of_notMem_tsupport (fun ht => hη (ψ.tsupport_subset ht)), mul_zero]
  have he := integral_localizedTruncation (μ := volume) (A := {η | ε < ν (C.Θ η ξ)})
    C.isOpen_U.measurableSet hz
  rw [← he, inter_comm]
  exact C.integral_sharp_inputChart hξ ν g ψ hν ε

end RothschildStein.P1.LiftedChart

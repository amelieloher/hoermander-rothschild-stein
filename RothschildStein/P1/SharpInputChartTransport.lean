-- Copyright (c) 2026 Scott Armstrong and Amélie Loher. All rights reserved.
-- Released under Apache 2.0 license as described in the file LICENSE.
module

public import RothschildStein.P1.ReflectedChartTransport

set_option autoImplicit false
set_option relaxedAutoImplicit false
@[expose] public section
noncomputable section
open Set MeasureTheory
namespace RothschildStein.P1.LiftedChart
variable {n k m : ℕ} {w : Fin k → ℕ+} {s : ℕ} {Ω : Set (Fin n → ℝ)}
  {hΩ : IsOpen Ω} {X : Fin k → (Fin n → ℝ) → (Fin n → ℝ)} {x₀ : Fin n → ℝ}
  {C : LiftedChart w s Ω hΩ X x₀ m}

/-- Sharp input-chart truncations agree exactly
with sharp model truncations and their full reflected density. -/
theorem integral_sharp_inputChart {ξ : Fin (n + m) → ℝ} (hξ : ξ ∈ C.U)
    (ν g ψ : (Fin (n + m) → ℝ) → ℝ) (hν : Continuous ν) (ε : ℝ) :
    (∫ η in C.U ∩ {η | ε < ν (C.Θ η ξ)}, g (C.Θ η ξ) * ψ η) =
      ∫ u in {u | ε < ν u}, g u * C.reflectedTransport ξ ψ u := by
  have hθ : ContinuousOn (fun η => C.Θ η ξ) C.U :=
    (C.theta_smooth.comp (contDiffOn_id.prodMk contDiffOn_const)
      (fun η hη => ⟨hη, hξ⟩)).continuousOn
  have ho : IsOpen (C.U ∩ {η | ε < ν (C.Θ η ξ)}) :=
    (hν.comp_continuousOn hθ).isOpen_inter_preimage C.isOpen_U isOpen_Ioi
  have hm : MeasurableSet {u | ε < ν u} :=
    measurableSet_lt measurable_const hν.measurable
  have he : (∫ η in C.U, ({u | ε < ν u}.indicator g) (C.Θ η ξ) * ψ η) =
      ∫ η in C.U ∩ {η | ε < ν (C.Θ η ξ)}, g (C.Θ η ξ) * ψ η := by
    rw [← integral_indicator ho.measurableSet]
    rw [← integral_indicator C.isOpen_U.measurableSet]
    congr 1
    funext η
    by_cases hη : η ∈ C.U
    · by_cases ht : ε < ν (C.Θ η ξ) <;> simp [hη, ht]
    · simp [hη]
  rw [← he, integral_input_theta_mul hξ, ← integral_indicator hm]
  congr 1
  funext u
  by_cases hu : ε < ν u <;> simp [hu]

end RothschildStein.P1.LiftedChart

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

/-- Bounded continuous model multipliers
preserve integrability of actual supported input chart rows. -/
theorem integrable_modelMultiplier {ξ : Fin (n+m) → ℝ} (hξ : ξ ∈ C.U)
    {f : (Fin (n+m) → ℝ) → ℝ} (hi : Integrable f)
    (hs : ∀ η, η ∉ C.U → f η = 0)
    (χ : (Fin (n+m) → ℝ) → ℝ) (hχ : Continuous χ)
    {B : ℝ} (hb : ∀ u, ‖χ u‖ ≤ B) :
    Integrable (fun η => χ (C.Θ η ξ) * f η) := by
  have hθ : ContinuousOn (fun η => C.Θ η ξ) C.U :=
    C.theta_smooth.continuousOn.comp
      (continuousOn_id.prodMk continuousOn_const) (fun _ hη => ⟨hη, hξ⟩)
  have hm := (hχ.comp_continuousOn hθ).aestronglyMeasurable (μ := volume)
    C.isOpen_U.measurableSet
  have hlocal := hi.integrableOn.bdd_mul hm (Filter.Eventually.of_forall (fun η => hb (C.Θ η ξ)))
  apply (integrableOn_iff_integrable_of_support_subset ?_).mp hlocal
  intro η hη
  by_contra hn
  exact hη (by
    change χ (C.Θ η ξ) * f η = 0
    rw [hs η hn, mul_zero])

end RothschildStein.P1.LiftedChart

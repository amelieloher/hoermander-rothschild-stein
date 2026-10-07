-- Copyright (c) 2026 Scott Armstrong and Amélie Loher. All rights reserved.
-- Released under Apache 2.0 license as described in the file LICENSE.
module
public import Mathlib.MeasureTheory.Integral.Bochner.Set
@[expose] public section
set_option autoImplicit false
set_option relaxedAutoImplicit false
noncomputable section
open Set MeasureTheory
namespace RothschildStein.H2
variable {X : Type*} [MeasurableSpace X]

/-- Enlarging an integration domain preserves integrability when
its added part has pointwise zero integrand. -/
theorem integrableOn_enlarge_zero {μ : Measure X} {s t : Set X}
    (hs : MeasurableSet s) (ht : MeasurableSet t) (hst : s ⊆ t) {g : X → ℝ}
    (hi : IntegrableOn g s μ) (hz : ∀ x ∈ t \ s, g x = 0) : IntegrableOn g t μ := by
  classical
  have he : s.indicator g = t.indicator g := by
    funext x
    by_cases hxs : x ∈ s
    · simp [hxs, hst hxs]
    by_cases hxt : x ∈ t
    · simp [hxs, hxt, hz x ⟨hxt, hxs⟩]
    · simp [hxs, hxt]
  apply (integrable_indicator_iff ht).mp
  rw [← he]
  exact hi.integrable_indicator hs
end RothschildStein.H2

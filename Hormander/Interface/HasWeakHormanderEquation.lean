-- Copyright (c) 2026 Scott Armstrong and Amélie Loher. All rights reserved.
-- Released under Apache 2.0 license as described in the file LICENSE.
module

public import Hormander.Interface.HormanderAdjointTest

@[expose] public section

noncomputable section

open Set MeasureTheory
open scoped BigOperators

namespace Hormander.Interface

/-- A locally integrable function satisfying the weak Hörmander equation
`X₀ u + Σ Xᵢ² u + c u = g`, tested against smooth compactly supported functions. -/
def HasWeakHormanderEquation {k N : ℕ} (Ω : Set (Fin N → ℝ))
    (X : Fin (k + 1) → (Fin N → ℝ) → (Fin N → ℝ))
    (c g u : (Fin N → ℝ) → ℝ) : Prop :=
  LocallyIntegrableOn u Ω volume ∧
    ContDiffOn ℝ (⊤ : ℕ∞) g Ω ∧
    ∀ φ : (Fin N → ℝ) → ℝ,
      ContDiff ℝ (⊤ : ℕ∞) φ →
      HasCompactSupport φ →
      tsupport φ ⊆ Ω →
      (∫ x in Ω, u x * hormanderAdjointTest X c φ x) =
        ∫ x in Ω, g x * φ x

end Hormander.Interface

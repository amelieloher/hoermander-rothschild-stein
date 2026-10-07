-- Copyright (c) 2026 Scott Armstrong and Amélie Loher. All rights reserved.
-- Released under Apache 2.0 license as described in the file LICENSE.
module

public import RothschildStein.H1.InterfaceDictionary
public import Hormander.Interface.HasWeakHormanderEquation

set_option autoImplicit false
set_option relaxedAutoImplicit false
set_option backward.isDefEq.respectTransparency false

@[expose] public section
noncomputable section
namespace RothschildStein.H1
open MeasureTheory
variable {N q : ℕ} (G : HomogeneousGroup N)

/-- The weak equation is the group transpose pairing equation
(BB Definition 6.16, p. 264). The smoothness required of g remains explicit. -/
theorem StandingHypotheses.hasWeakHormanderEquation_iff (H : StandingHypotheses G q)
    (U : Set (Fin N → ℝ)) (g u : (Fin N → ℝ) → ℝ) :
    Hormander.Interface.HasWeakHormanderEquation U H.fields 0 g u ↔
      LocallyIntegrableOn u U volume ∧ ContDiffOn ℝ (⊤ : ℕ∞) g U ∧
      ∀ φ : (Fin N → ℝ) → ℝ, ContDiff ℝ (⊤ : ℕ∞) φ → HasCompactSupport φ → tsupport φ ⊆ U →
        (∫ x in U, u x * sumSquaresWithDriftTranspose H.fields φ x) = ∫ x in U, g x * φ x := by
  constructor
  · rintro ⟨hu, hg, he⟩
    refine ⟨hu, hg, ?_⟩
    intro φ hφ hc hs
    have h := he φ hφ hc hs
    simpa only [H.hormanderAdjointTest_eq_transpose G φ hφ] using h
  · rintro ⟨hu, hg, he⟩
    refine ⟨hu, hg, ?_⟩
    intro φ hφ hc hs
    simpa only [H.hormanderAdjointTest_eq_transpose G φ hφ] using he φ hφ hc hs

end RothschildStein.H1

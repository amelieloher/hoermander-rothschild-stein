-- Copyright (c) 2026 Scott Armstrong and Amélie Loher. All rights reserved.
-- Released under Apache 2.0 license as described in the file LICENSE.
module
public import RothschildStein.L1.DirectEvaluationBasis
@[expose] public section
set_option autoImplicit false
set_option relaxedAutoImplicit false
noncomputable section
open Set TopologicalSpace
namespace RothschildStein.L1
open G3

/-- Every fixed formal commutator evaluates to a smooth field. -/
theorem directPointEvaluation_contDiffOn {a s N : ℕ} {p : Fin a → ℕ+}
    (Ω : Opens (Fin N → ℝ)) (X : Fin a → (Fin N → ℝ) → (Fin N → ℝ))
    (hX : ∀ i, ContDiffOn ℝ (⊤ : ℕ∞) (X i) Ω) (f : formalSpan a s p) :
    ContDiffOn ℝ (⊤ : ℕ∞) (fun x => directPointEvaluation (s := s) (p := p) Ω X hX x f) Ω := by
  apply contDiffOn_pi.mpr
  intro j
  exact ((differentialWordEvaluation Ω X hX (finitePolynomialLinear f.val)) (coordinateTest Ω j)).property
end RothschildStein.L1

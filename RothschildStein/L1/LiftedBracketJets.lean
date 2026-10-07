-- Copyright (c) 2026 Scott Armstrong and Amélie Loher. All rights reserved.
-- Released under Apache 2.0 license as described in the file LICENSE.
module
public import RothschildStein.L1.LiftedJetRealization
public import RothschildStein.L1.DirectEvaluation
public import RothschildStein.G3.DifferentialPolynomialBounds
@[expose] public section
set_option autoImplicit false
set_option relaxedAutoImplicit false
noncomputable section
open Set TopologicalSpace
open scoped BigOperators
namespace RothschildStein.L1

/-- The vertical component of an actual bounded bracket is the
formal associative coefficient vector paired with the prescribed ordered
vertical jets (BB Proposition 10.17, (10.8)). -/
theorem wordBracket_vertical_of_ordered_jets {a s n : ℕ} {p : Fin a → ℕ+}
    (Ω : Opens (Fin (n+1) → ℝ))
    (Y : Fin a → (Fin (n+1) → ℝ) → (Fin (n+1) → ℝ))
    (hY : ∀ i, ContDiffOn ℝ (⊤ : ℕ∞) (Y i) Ω)
    {ξ : Fin (n+1) → ℝ} (hξ : ξ ∈ Ω) (d : List (Fin a) → ℝ)
    (hjets : ∀ J : List (Fin a), wordWeight p J ≤ s →
      wordDerivative Y J (fun η => P1.paddingFiberCLM n 1 η 0) ξ = d J)
    (I : List (Fin a)) (hI : wordWeight p I ≤ s) :
    P1.paddingFiberCLM n 1 (wordBracket Y I ξ) 0 =
      ∑ J : BoundedWord a s p, truncatedBracket I J * d (boundedWordList J) := by
  classical
  have he := congrArg (fun v : Fin (n+1) → ℝ => v (Fin.natAdd n (0 : Fin 1)))
    (directPointEvaluation_word (s := s) (p := p) Ω Y hY I hI hξ)
  change (G3.differentialWordEvaluation Ω Y hY
    (G3.finitePolynomial (truncatedBracket I))
    (coordinateTest Ω (Fin.natAdd n (0 : Fin 1)))).val ξ = _ at he
  rw [G3.differentialWordEvaluation_finitePolynomial_apply Ω Y hY _ _ hξ] at he
  change wordBracket Y I ξ (Fin.natAdd n (0 : Fin 1)) = _
  rw [← he]
  apply Finset.sum_congr rfl
  intro J _
  change truncatedBracket I J * wordDerivative Y (boundedWordList J)
    (fun η => P1.paddingFiberCLM n 1 η 0) ξ = _
  rw [hjets _ (G3.boundedWord_weight J)]
end RothschildStein.L1

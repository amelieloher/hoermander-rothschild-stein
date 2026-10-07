-- Copyright (c) 2026 Scott Armstrong and Amélie Loher. All rights reserved.
-- Released under Apache 2.0 license as described in the file LICENSE.
module
public import RothschildStein.G3.WeightedWordBounds
public import RothschildStein.G3.DifferentialWordEvaluation
@[expose] public section
noncomputable section
open Set TopologicalSpace
open scoped BigOperators
namespace RothschildStein.G3

/-- Evaluation of a finite coefficient polynomial is the finite sum
of the actual ordered field-word derivatives (BB Lemma 9.22, pp. 413–414). -/
theorem differentialWordEvaluation_finitePolynomial_apply {a s N : ℕ}
    {p : Fin a → ℕ+} (Ω : Opens (Fin N → ℝ))
    (X : Fin a → (Fin N → ℝ) → (Fin N → ℝ))
    (hX : ∀ i, ContDiffOn ℝ (⊤ : ℕ∞) (X i) Ω)
    (A : WordCoefficients a s p) (f : smoothOnFunctions Ω)
    {x : Fin N → ℝ} (hx : x ∈ Ω) :
    (differentialWordEvaluation Ω X hX (finitePolynomial A) f).val x =
      ∑ J : BoundedWord a s p, A J * wordDerivative X J.val f.val x := by
  classical
  rw [finitePolynomial, map_sum]
  simp only [LinearMap.sum_apply, Submodule.coe_sum, Finset.sum_apply]
  change (∑ J : BoundedWord a s p,
    (differentialWordEvaluation Ω X hX
      (MonoidAlgebra.single (FreeMonoid.ofList J.val) (A J)) f).val x) = _
  apply Finset.sum_congr rfl
  intro J _
  exact differentialWordEvaluation_single Ω X hX J.val (A J) f hx

end RothschildStein.G3

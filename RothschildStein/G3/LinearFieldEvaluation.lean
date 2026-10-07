-- Copyright (c) 2026 Scott Armstrong and Amélie Loher. All rights reserved.
-- Released under Apache 2.0 license as described in the file LICENSE.
module
public import RothschildStein.G3.LinearWordPolynomials
public import RothschildStein.G4.TimeOneFlow
@[expose] public section
noncomputable section
open Set TopologicalSpace
open scoped BigOperators
namespace RothschildStein.G3

/-- Linear word input evaluates to the actual differential operator
of the constant field combination (BB Lemma 9.22, pp. 413–414). -/
theorem differentialWordEvaluation_linearWordPolynomial {a N : ℕ}
    (Ω : Opens (Fin N → ℝ))
    (X : Fin a → (Fin N → ℝ) → (Fin N → ℝ))
    (hX : ∀ i, ContDiffOn ℝ (⊤ : ℕ∞) (X i) Ω) (c : Fin a → ℝ) :
    differentialWordEvaluation Ω X hX (linearWordPolynomial c) =
      smoothFieldOperator Ω (fun x => ∑ i, c i • X i x)
        (ContDiffOn.sum (fun i _ => (hX i).const_smul (c i))) := by
  classical
  simp only [linearWordPolynomial, map_sum, differentialWordEvaluation,
    MonoidAlgebra.lift_single, FreeMonoid.lift_eval_of]
  apply LinearMap.ext
  intro f
  apply Subtype.ext
  funext x
  simp only [LinearMap.sum_apply, LinearMap.smul_apply,
    Submodule.coe_sum, Submodule.coe_smul_of_tower, Finset.sum_apply, Pi.smul_apply]
  change (∑ i, c i • (if x ∈ Ω then (fderiv ℝ f.val x) (X i x) else 0)) =
    (if x ∈ Ω then (fderiv ℝ f.val x) (∑ i, c i • X i x) else 0)
  by_cases hx : x ∈ Ω
  · simp only [ite_eq_left hx, map_sum, map_smul]
  · simp only [ite_eq_right hx, smul_zero, Finset.sum_const_zero]
end RothschildStein.G3

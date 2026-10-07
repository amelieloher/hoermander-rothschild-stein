-- Copyright (c) 2026 Scott Armstrong and Amélie Loher. All rights reserved.
-- Released under Apache 2.0 license as described in the file LICENSE.
module
public import RothschildStein.G3.FieldPowerLocality
public import RothschildStein.G3.WordPolynomialExponential
@[expose] public section
noncomputable section
open Set TopologicalSpace
open scoped BigOperators
namespace RothschildStein.G3

/-- Actual evaluation of a finite exponential product equals the
ordered rectangular two-flow Taylor polynomial (BB (9.10), p. 411). -/
theorem differentialWordEvaluation_exponentialProduct {a N : ℕ}
    (Ω : Opens (Fin N → ℝ))
    (X : Fin a → (Fin N → ℝ) → (Fin N → ℝ))
    (hX : ∀ i, ContDiffOn ℝ (⊤ : ℕ∞) (X i) Ω)
    (P Q : MonoidAlgebra ℝ (FreeMonoid (Fin a)))
    (U V : (Fin N → ℝ) → (Fin N → ℝ))
    (hU : ContDiffOn ℝ (⊤ : ℕ∞) U Ω) (hV : ContDiffOn ℝ (⊤ : ℕ∞) V Ω)
    (hP : differentialWordEvaluation Ω X hX P = smoothFieldOperator Ω U hU)
    (hQ : differentialWordEvaluation Ω X hX Q = smoothFieldOperator Ω V hV)
    (m n : ℕ) (f : smoothOnFunctions Ω) {x : Fin N → ℝ} (hx : x ∈ Ω) :
    (differentialWordEvaluation Ω X hX (wordPolynomialExp P m * wordPolynomialExp Q n) f).val x =
      ∑ k ∈ Finset.range (n + 1), (k.factorial : ℝ)⁻¹ *
        (∑ j ∈ Finset.range (m + 1), (j.factorial : ℝ)⁻¹ *
          fieldPower U j (fieldPower V k f.val) x) := by
  simp only [wordPolynomialExp, map_mul, map_sum, map_smul, map_pow, hP, hQ,
    Finset.sum_mul, Finset.mul_sum, smul_mul_assoc, mul_smul_comm,
    LinearMap.sum_apply, LinearMap.smul_apply, Submodule.coe_sum,
    Submodule.coe_smul_of_tower, Finset.sum_apply, Pi.smul_apply, smul_eq_mul]
  apply Finset.sum_congr rfl
  intro k _
  apply Finset.sum_congr rfl
  intro j _
  rw [smoothFieldOperator_mixed_pow_apply Ω U V hU hV j k f hx]
end RothschildStein.G3

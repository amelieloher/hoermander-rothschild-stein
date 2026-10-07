-- Copyright (c) 2026 Scott Armstrong and Amélie Loher. All rights reserved.
-- Released under Apache 2.0 license as described in the file LICENSE.
module
public import RothschildStein.G3.WeightedPolynomialTail
@[expose] public section
noncomputable section
open Set TopologicalSpace
open scoped BigOperators
namespace RothschildStein.G3

/-- Polynomial operator bounds need jets only through the ordinary
length of nonzero terms, even if the weighted cutoff is much larger. In a
basis-word alphabet this avoids expanding products of bracket fields into
unnecessarily long primitive differential words (BB Lemma 9.22, pp. 413–414). -/
theorem norm_weighted_polynomial_le_of_support_length {a s N R : ℕ}
    {p : Fin a → ℕ+} (Ω : Opens (Fin N → ℝ))
    (X : Fin a → (Fin N → ℝ) → (Fin N → ℝ))
    (hX : ∀ i, ContDiffOn ℝ (⊤ : ℕ∞) (X i) Ω)
    (δ : ℝ) (A : WordCoefficients a s p) (f : smoothOnFunctions Ω)
    {x : Fin N → ℝ} (hx : x ∈ Ω) {B F : ℝ} (hB : 0 ≤ B)
    (hXjet : ∀ i, ∀ j ≤ R, ‖iteratedFDeriv ℝ j (X i) x‖ ≤ B)
    (hfjet : ∀ j ≤ R, ‖iteratedFDeriv ℝ j f.val x‖ ≤ F)
    (hlen : ∀ J, A J ≠ 0 → J.val.length ≤ R) :
    ‖differentialWordEvaluation Ω (fun i => δ ^ (p i : ℕ) • X i)
        (fun i => ((hX i).const_smul (δ ^ (p i : ℕ))).congr (fun x _ => by ext j; rfl))
        (finitePolynomial A) f |>.val x‖ ≤
      ∑ J : BoundedWord a s p,
        |A J| * (|δ| ^ wordWeight p J.val * ((2 ^ R * B) ^ J.val.length * F)) := by
  rw [differentialWordEvaluation_finitePolynomial_apply Ω _ _ A f hx]
  apply (norm_sum_le _ _).trans
  apply Finset.sum_le_sum
  intro J _
  rw [norm_mul, Real.norm_eq_abs]
  by_cases hJ : A J = 0
  · simp only [hJ, abs_zero, zero_mul, le_refl]
  · apply mul_le_mul_of_nonneg_left _ (abs_nonneg _)
    have hh := norm_weighted_wordDerivative_jet_le Ω X hX p δ J.val f.val f.property
      hx hB hXjet hfjet 0 (by simpa using hlen J hJ)
    simpa only [norm_iteratedFDeriv_zero] using hh

/-- A discarded weighted polynomial has the requested small factor
using only its nonzero terms' ordinary-length jet budget (BB pp. 413–415). -/
theorem norm_weighted_polynomial_tail_le_of_support_length {a s N R k : ℕ}
    {p : Fin a → ℕ+} (Ω : Opens (Fin N → ℝ))
    (X : Fin a → (Fin N → ℝ) → (Fin N → ℝ))
    (hX : ∀ i, ContDiffOn ℝ (⊤ : ℕ∞) (X i) Ω)
    (δ : ℝ) (A : WordCoefficients a s p) (f : smoothOnFunctions Ω)
    {x : Fin N → ℝ} (hx : x ∈ Ω) {B F : ℝ} (hB : 0 ≤ B)
    (hXjet : ∀ i, ∀ j ≤ R, ‖iteratedFDeriv ℝ j (X i) x‖ ≤ B)
    (hfjet : ∀ j ≤ R, ‖iteratedFDeriv ℝ j f.val x‖ ≤ F)
    (hlen : ∀ J, A J ≠ 0 → J.val.length ≤ R) (hδ : |δ| ≤ 1)
    (hA : ∀ J, wordWeight p J.val < k → A J = 0) :
    ‖differentialWordEvaluation Ω (fun i => δ ^ (p i : ℕ) • X i)
        (fun i => ((hX i).const_smul (δ ^ (p i : ℕ))).congr (fun x _ => by ext j; rfl))
        (finitePolynomial A) f |>.val x‖ ≤
      |δ| ^ k * ∑ J : BoundedWord a s p, |A J| * ((2 ^ R * B) ^ J.val.length * F) := by
  have hF : 0 ≤ F := (norm_nonneg _).trans (hfjet 0 (Nat.zero_le R))
  exact (norm_weighted_polynomial_le_of_support_length Ω X hX δ A f hx hB hXjet hfjet hlen).trans
    (weighted_polynomial_tail_bound A _
      (fun J => mul_nonneg (pow_nonneg (mul_nonneg (by positivity) hB) _) hF) hδ hA)
end RothschildStein.G3

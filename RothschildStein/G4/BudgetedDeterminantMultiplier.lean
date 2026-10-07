-- Copyright (c) 2026 Scott Armstrong and Amélie Loher. All rights reserved.
-- Released under Apache 2.0 license as described in the file LICENSE.
module

public import RothschildStein.G4.DivergenceJetBounds
public import RothschildStein.G4.BudgetedExpansionProducts

@[expose] public section
set_option autoImplicit false
set_option relaxedAutoImplicit false
noncomputable section
open Set
open scoped BigOperators

namespace RothschildStein.G4

/-- The actual determinant multiplier has an explicit numerical
coefficient-jet budget, with one generator factor and its signed deficit. -/
theorem determinantMultiplier_budget {k n s : ℕ}
    {Ω K₀ : Set (Fin n → ℝ)} (hΩ : IsOpen Ω) (hKΩ : K₀ ⊆ Ω) {w : Fin (k + 1) → ℕ+}
    {X : Fin (k + 1) → (Fin n → ℝ) → (Fin n → ℝ)}
    (hX : ∀ i, ContDiffOn ℝ (⊤ : ℕ∞) (X i) Ω)
    (hstep : bracketStepOn Ω w X s) (B : Fin n → ShortWord w s) (L : ShortWord w s)
    {h : ℕ} {P A : ℝ} (hP : 0 ≤ P) (hA : 0 ≤ A)
    (hZP : HasJetBound Ω K₀ (shortField w X L) (h + 1) P)
    (hcA : ∀ J K : ShortWord w s, HasJetBound Ω K₀ (shortBracketCoefficient w X L J K) h A) :
    HasBudgetedGeneratorExpansion Ω K₀ (shortField w X) (shortWeight w) B 1
      (-((shortWeight w L : ℕ) : ℤ)) h (determinantMultiplier w X B L)
      (divergenceJetMultiplier n * P + n * Fintype.card (ShortWord w s) * A) := by
  classical
  let Z := shortField (s := s) w X
  let v := shortWeight (s := s) w
  have hneg : -((v L : ℕ) : ℤ) ≤ 0 := neg_nonpos.mpr (by positivity)
  have hd := HasBudgetedGeneratorExpansion.term (Hormander.Interface.euclideanDivergence (Z L))
    (fun _ => 1) (divergenceJetMultiplier n * P)
    (mul_nonneg (divergenceJetMultiplier_nonneg n) hP) (divergence_contDiffOn hΩ (shortField_contDiffOn hΩ hX L))
      (hZP.divergence hΩ hKΩ (shortField_contDiffOn hΩ hX L))
      (generator_one Z v B 1 hneg)
  have hd' : HasBudgetedGeneratorExpansion Ω K₀ Z v B 1 (-((v L : ℕ) : ℤ))
      h (Hormander.Interface.euclideanDivergence (Z L)) (divergenceJetMultiplier n * P) :=
    hd.congr (fun x _ => (mul_one _).symm)
  have hterm : ∀ j : Fin n, ∀ K : ShortWord w s,
      HasBudgetedGeneratorExpansion Ω K₀ Z v B 1 (-((v L : ℕ) : ℤ))
        h (fun x => shortBracketCoefficient w X L (B j) K x * frameCoefficient Z B (Z K) j x) A := by
    intro j K
    by_cases hweight : (v L : ℕ) + (v (B j) : ℕ) < (v K : ℕ)
    · have hc := shortBracketCoefficient_eq_zero_of_weight_lt w X L (B j) K hweight
      exact (HasBudgetedGeneratorExpansion.zero.enlarge hA).congr (fun x _ => by
        simp only [congrFun hc x, Pi.zero_apply, zero_mul])
    · have hw : (v K : ℕ) ≤ (v L : ℕ) + (v (B j) : ℕ) := le_of_not_gt hweight
      have hw' : ((v K : ℕ) : ℤ) ≤ ((v L : ℕ) : ℤ) + ((v (B j) : ℕ) : ℤ) := by exact_mod_cast hw
      exact HasBudgetedGeneratorExpansion.term _ _ A hA (shortBracketCoefficient_contDiffOn hΩ hX hstep L (B j) K)
        (hcA (B j) K)
        (generator_mono le_rfl (by omega) (frameCoefficient_isGenerator Z v B j K))
  have hh := HasBudgetedGeneratorExpansion.add hd' (budgetedExpansion_sum Finset.univ _ _ (fun j _ =>
    budgetedExpansion_sum Finset.univ _ _ (fun K _ => hterm j K)))
  change HasBudgetedGeneratorExpansion Ω K₀ Z v B 1 (-((v L : ℕ) : ℤ)) h
    (fun x => Hormander.Interface.euclideanDivergence (Z L) x +
      ∑ j, ∑ K, shortBracketCoefficient w X L (B j) K x * frameCoefficient Z B (Z K) j x) _
  simpa only [Finset.sum_const, Finset.card_univ, nsmul_eq_mul, Fintype.card_fin, mul_assoc] using hh

end RothschildStein.G4

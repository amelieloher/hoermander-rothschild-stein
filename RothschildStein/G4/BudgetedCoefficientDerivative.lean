-- Copyright (c) 2026 Scott Armstrong and Amélie Loher. All rights reserved.
-- Released under Apache 2.0 license as described in the file LICENSE.
module

public import RothschildStein.G4.ShortBracketReduction
public import RothschildStein.G4.BudgetedExpansionProducts
public import RothschildStein.G4.GeneratorProducts

@[expose] public section
set_option autoImplicit false
set_option relaxedAutoImplicit false
noncomputable section
open Set
open scoped BigOperators

namespace RothschildStein.G4

/-- The actual differentiated frame coefficient has an explicit
finite-jet expansion budget, at most two factors, and exactly the
differentiating field's weight loss
(BB Proposition 9.36, pp. 427–428). -/
theorem short_frameCoefficient_derivative_budget {k n s : ℕ}
    {Ω K₀ : Set (Fin n → ℝ)} (hΩ : IsOpen Ω) (hKΩ : K₀ ⊆ Ω) {w : Fin (k + 1) → ℕ+}
    {X : Fin (k + 1) → (Fin n → ℝ) → (Fin n → ℝ)}
    (hX : ∀ i, ContDiffOn ℝ (⊤ : ℕ∞) (X i) Ω)
    (hstep : bracketStepOn Ω w X s) (B : Fin n → ShortWord w s)
    (L J : ShortWord w s) (i : Fin n) {h : ℕ} {M : ℝ} (hM : 0 ≤ M)
    (hjets : ∀ L J K : ShortWord w s,
      HasJetBound Ω K₀ (shortBracketCoefficient w X L J K) h M) :
    HasBudgetedGeneratorExpansion Ω K₀ (shortField w X) (shortWeight w) B 2
      (((shortWeight w (B i) : ℕ) : ℤ) - ((shortWeight w J : ℕ) : ℤ) -
        ((shortWeight w L : ℕ) : ℤ))
      h (fieldDerivative (shortField w X L)
        (frameCoefficient (shortField w X) B (shortField w X J) i))
      ((Fintype.card (ShortWord w s) : ℝ) * ((n : ℝ) + 1) * M) := by
  classical
  let Z := shortField (s := s) w X
  let v := shortWeight (s := s) w
  let p : ℤ := ((v (B i) : ℕ) : ℤ) - ((v J : ℕ) : ℤ) - ((v L : ℕ) : ℤ)
  have hfirst : ∀ K : ShortWord w s,
      HasBudgetedGeneratorExpansion Ω K₀ Z v B 2 p h
        (fun x => shortBracketCoefficient w X L J K x * frameCoefficient Z B (Z K) i x) M := by
    intro K
    by_cases hweight : (v L : ℕ) + (v J : ℕ) < (v K : ℕ)
    · have hc := shortBracketCoefficient_eq_zero_of_weight_lt w X L J K hweight
      exact (HasBudgetedGeneratorExpansion.zero.enlarge hM).congr (fun x _ => by simp only [congrFun hc x, Pi.zero_apply, zero_mul])
    · have hw : (v K : ℕ) ≤ (v L : ℕ) + (v J : ℕ) := le_of_not_gt hweight
      have hw' : ((v K : ℕ) : ℤ) ≤ ((v L : ℕ) : ℤ) + ((v J : ℕ) : ℤ) := by exact_mod_cast hw
      have hg := generator_mono (show 1 ≤ 2 by omega)
        (show p ≤ ((v (B i) : ℕ) : ℤ) - ((v K : ℕ) : ℤ) by dsimp [p]; omega)
        (frameCoefficient_isGenerator Z v B i K)
      exact HasBudgetedGeneratorExpansion.term _ _ M hM
        (shortBracketCoefficient_contDiffOn hΩ hX hstep L J K) (hjets L J K) hg
  have hsecond : ∀ j : Fin n, ∀ K : ShortWord w s,
      HasBudgetedGeneratorExpansion Ω K₀ Z v B 2 p h
        (fun x => shortBracketCoefficient w X L (B j) K x *
          (frameCoefficient Z B (Z J) j x * frameCoefficient Z B (Z K) i x)) M := by
    intro j K
    by_cases hweight : (v L : ℕ) + (v (B j) : ℕ) < (v K : ℕ)
    · have hc := shortBracketCoefficient_eq_zero_of_weight_lt w X L (B j) K hweight
      exact (HasBudgetedGeneratorExpansion.zero.enlarge hM).congr (fun x _ => by simp only [congrFun hc x, Pi.zero_apply, zero_mul])
    · have hw : (v K : ℕ) ≤ (v L : ℕ) + (v (B j) : ℕ) := le_of_not_gt hweight
      have hw' : ((v K : ℕ) : ℤ) ≤ ((v L : ℕ) : ℤ) + ((v (B j) : ℕ) : ℤ) := by exact_mod_cast hw
      have hg := generator_mul (frameCoefficient_isGenerator Z v B j J)
        (frameCoefficient_isGenerator Z v B i K)
      have hg' := generator_mono (show 1 + 1 ≤ 2 by omega)
        (show p ≤ (((v (B j) : ℕ) : ℤ) - ((v J : ℕ) : ℤ)) +
          (((v (B i) : ℕ) : ℤ) - ((v K : ℕ) : ℤ)) by dsimp [p]; omega) hg
      exact HasBudgetedGeneratorExpansion.term _ _ M hM
        (shortBracketCoefficient_contDiffOn hΩ hX hstep L (B j) K) (hjets L (B j) K) hg'
  have hf := budgetedExpansion_sum Finset.univ _ (fun _ => M) (fun K _ => hfirst K)
  have hs := budgetedExpansion_sum Finset.univ _ (fun _ => ∑ _ : ShortWord w s, M)
    (fun j _ => budgetedExpansion_sum Finset.univ _ (fun _ => M) (fun K _ => hsecond j K))
  have hb := (HasBudgetedGeneratorExpansion.add hf (budgetedExpansion_neg hΩ hKΩ hs)).congr
    (g := fieldDerivative (shortField w X L)
      (frameCoefficient (shortField w X) B (shortField w X J) i))
    (fun x hx => by simpa only [sub_eq_add_neg] using
      short_fieldDerivative_frameCoefficient hΩ hX hstep B L J i hx.1 hx.2)
  convert hb using 1
  simp only [Finset.sum_const, Finset.card_univ, nsmul_eq_mul, Fintype.card_fin]
  ring

end RothschildStein.G4

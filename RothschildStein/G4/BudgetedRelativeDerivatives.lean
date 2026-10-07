-- Copyright (c) 2026 Scott Armstrong and Amélie Loher. All rights reserved.
-- Released under Apache 2.0 license as described in the file LICENSE.
module

public import RothschildStein.G4.BudgetedExpansionDifferentiation
public import RothschildStein.G4.RelativeDerivatives
public import RothschildStein.G4.BudgetedDeterminantMultiplier

@[expose] public section
set_option autoImplicit false
set_option relaxedAutoImplicit false
noncomputable section
open Set

namespace RothschildStein.G4

/-- Explicit coefficient-budget recurrence for ordered derivatives. -/
def relativeExpansionBudget (n p h a : ℕ) (P A Q : ℝ) : ℕ → ℝ
  | 0 => 1
  | l + 1 => relativeExpansionBudget n p (h + 1) a P A Q l *
      (expansionDerivativeBudget n p h (a + l) P A + scalarJetMultiplier h * Q)

/-- The iterated budget recurrence is nonnegative. -/
theorem relativeExpansionBudget_nonneg (n p h a l : ℕ) {P A Q : ℝ}
    (hP : 0 ≤ P) (hA : 0 ≤ A) (hQ : 0 ≤ Q) : 0 ≤ relativeExpansionBudget n p h a P A Q l := by
  induction l generalizing h with
  | zero => exact zero_le_one
  | succ l ih => exact mul_nonneg (ih (h + 1)) (add_nonneg (expansionDerivativeBudget_nonneg n p h (a + l) hP hA)
      (mul_nonneg (scalarJetMultiplier_nonneg h) hQ))

/-- Ordered differentiation consumes exactly its number of input
coefficient jets and propagates a universal numerical budget. -/
theorem budgetedExpansion_relativeDerivatives {k n s : ℕ}
    {Ω K₀ : Set (Fin n → ℝ)} (hΩ : IsOpen Ω) (hKΩ : K₀ ⊆ Ω)
    {w : Fin (k + 1) → ℕ+} {X : Fin (k + 1) → (Fin n → ℝ) → (Fin n → ℝ)}
    (hX : ∀ i, ContDiffOn ℝ (⊤ : ℕ∞) (X i) Ω)
    (hstep : bracketStepOn Ω w X s) (B : Fin n → ShortWord w s)
    (M : List (ShortWord w s)) {a h : ℕ} {p : ℤ} {f : (Fin n → ℝ) → ℝ} {C P A Q : ℝ}
    (hP : 0 ≤ P) (hA : 0 ≤ A) (_hQ : 0 ≤ Q)
    (hZP : ∀ L : ShortWord w s, HasJetBound Ω K₀ (shortField w X L) (h + M.length) P)
    (hjets : ∀ L J K : ShortWord w s,
      HasJetBound Ω K₀ (shortBracketCoefficient w X L J K) (h + M.length) A)
    (hPQ : divergenceJetMultiplier n * P + n * Fintype.card (ShortWord w s) * A ≤ Q)
    (hf : HasBudgetedGeneratorExpansion Ω K₀ (shortField w X) (shortWeight w) B a p
      (h + M.length) f C) :
    HasBudgetedGeneratorExpansion Ω K₀ (shortField w X) (shortWeight w) B (a + M.length)
      (p - derivativeWeight (shortWeight w) M) h (relativeDerivatives w X B M f)
      (C * relativeExpansionBudget n (Fintype.card (ShortWord w s)) h a P A Q M.length) := by
  induction M generalizing h with
  | nil => simpa only [relativeDerivatives, derivativeWeight, List.map_nil, List.sum_nil,
      List.length_nil, add_zero, sub_zero, relativeExpansionBudget, mul_one] using hf
  | cons L M ih =>
    have he : (h + 1) + M.length = h + (L :: M).length := by simp only [List.length_cons]; omega
    have hb := ih (h := h + 1)
      (fun L => by simpa only [he] using hZP L)
      (fun L J K => by simpa only [he] using hjets L J K)
      (by simpa only [he] using hf)
    have hd := budgetedExpansion_derivative hΩ hKΩ hX hstep B L hP hA
      ((hZP L).mono (Nat.le_add_right _ _))
      (fun L J K => (hjets L J K).mono (Nat.le_add_right _ _)) hb
    have hm₀ := (determinantMultiplier_budget hΩ hKΩ hX hstep B L hP hA
      ((hZP L).mono (by simp only [List.length_cons]; omega))
      (fun J K => (hjets L J K).mono (Nat.le_add_right _ _))).enlarge hPQ
    have hm := budgetedExpansion_mul hΩ hKΩ
      (budgetedExpansion_mono le_rfl le_rfl (Nat.le_succ _) hb) hm₀
    have hm' : HasBudgetedGeneratorExpansion Ω K₀ (shortField w X) (shortWeight w) B
        (a + M.length + 1) (p - derivativeWeight (shortWeight w) M - ((shortWeight w L : ℕ) : ℤ)) h
        (fun x => relativeDerivatives w X B M f x * determinantMultiplier w X B L x)
        (scalarJetMultiplier h * (C * relativeExpansionBudget n (Fintype.card (ShortWord w s))
          (h + 1) a P A Q M.length) * Q) := by
      convert hm using 1
      omega
    have hh := HasBudgetedGeneratorExpansion.add hd hm'
    convert hh using 1
    · simp only [derivativeWeight, List.map_cons, List.sum_cons]
      omega
    · rfl
    · simp only [List.length_cons, relativeExpansionBudget]
      ring

end RothschildStein.G4

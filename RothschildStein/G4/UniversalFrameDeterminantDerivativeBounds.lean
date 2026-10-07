-- Copyright (c) 2026 Scott Armstrong and Amélie Loher. All rights reserved.
-- Released under Apache 2.0 license as described in the file LICENSE.
module

public import RothschildStein.G4.BudgetedRelativeDerivatives
public import RothschildStein.G4.ShortBracketJetBounds
public import RothschildStein.G4.BudgetedCoordinateDeterminant

@[expose] public section
set_option autoImplicit false
set_option relaxedAutoImplicit false
noncomputable section
open Set
open scoped BigOperators

namespace RothschildStein.G4

/-- Universal sharp determinant derivative bounds relative to a selected frame from a finite
input coefficient-jet budget. The constant is chosen before the spatial
sets, vector fields, frame, generator and differentiation word; only the
fixed combinatorial family and numerical data enter. -/
theorem exists_universal_frame_determinant_derivative_bound (k n s l : ℕ)
    (w : Fin (k + 1) → ℕ+) (M Δ : ℝ) (hM : 0 ≤ M) (hΔ : 0 < Δ) :
    ∃ C : ℝ, 0 < C ∧ ∀ (Ω K₀ : Set (Fin n → ℝ)), IsOpen Ω → K₀ ⊆ Ω →
      ∀ (X : Fin (k + 1) → (Fin n → ℝ) → (Fin n → ℝ)),
      (∀ i, ContDiffOn ℝ (⊤ : ℕ∞) (X i) Ω) → bracketStepOn Ω w X s →
      (∀ i, HasJetBound Ω K₀ (X i) (l + 2 * s) M) →
      (∀ x ∈ K₀, Δ ^ 2 ≤ determinantSquareSum (shortField (s := s) w X) x) →
      ∀ (B B' : Fin n → ShortWord w s) (L : List (ShortWord w s)), L.length ≤ l →
      ∀ x ∈ K₀, ∀ t r : ℝ, 0 < t → t ≤ 1 → 0 < r → r ≤ 1 →
        IsSuboptimal (shortField w X) (shortWeight w) B x t r →
        |shortDerivatives (shortField w X) L (frameDet (shortField w X) B') x| ≤
          C * t⁻¹ ^ (n + L.length) * r ^
            (frameWeight (shortWeight w) B - frameWeight (shortWeight w) B' - derivativeWeight (shortWeight w) L) *
            |frameDet (shortField w X) B x| := by
  obtain ⟨A, hA, hbracket⟩ := exists_shortBracketCoefficient_jet_bound k n s l w M Δ hM hΔ
  let P := wordJetBase n l s M ^ s
  have hP : 0 ≤ P := pow_nonneg (wordJetBase_nonneg_and_le hM).1 _
  let Q := divergenceJetMultiplier n * P + n * Fintype.card (ShortWord w s) * A
  have hQ : 0 ≤ Q := add_nonneg (mul_nonneg (divergenceJetMultiplier_nonneg n) hP)
    (mul_nonneg (mul_nonneg (Nat.cast_nonneg n) (Nat.cast_nonneg _)) hA.le)
  let D := fun j => relativeExpansionBudget n (Fintype.card (ShortWord w s)) 0 n P A Q j
  let C := 1 + (n.factorial : ℝ) * ∑ j ∈ Finset.range (l + 1), D j
  have hD : ∀ j, 0 ≤ D j := fun j => relativeExpansionBudget_nonneg n _ 0 n j hP hA.le hQ
  have hsum : 0 ≤ ∑ j ∈ Finset.range (l + 1), D j := Finset.sum_nonneg (fun j _ => hD j)
  have hfac : 0 ≤ (n.factorial : ℝ) := Nat.cast_nonneg _
  refine ⟨C, by dsimp [C]; nlinarith, ?_⟩
  intro Ω K₀ hΩ hKΩ X hX hstep hjets hdet B B' L hL x hx t r ht ht1 hr hr1 hB
  have hZP : ∀ J : ShortWord w s, HasJetBound Ω K₀ (shortField w X J) l P := by
    intro J
    have hJ := ((mem_shortWordFamily_iff w J.val).mp J.property).2
    exact wordBracket_jet_bound_uniform hΩ hKΩ X hX hM
      (fun i => (hjets i).mono (by omega)) J.val ((wordLength_le_wordWeight w J.val).trans hJ)
  have hAjet := hbracket Ω K₀ hΩ hKΩ X hX hstep hjets hdet
  have hf := coordinateDet_budget Ω K₀ (shortField w X) (shortWeight w) B B' (0 + L.length)
  have hb := budgetedExpansion_relativeDerivatives hΩ hKΩ hX hstep B L hP hA.le hQ
    (fun J => (hZP J).mono (by omega))
    (fun J J' K => (hAjet J J' K).mono (by omega)) le_rfl hf
  have hDC : (n.factorial : ℝ) * D L.length ≤ C := by
    have he := Finset.single_le_sum (fun j _ => hD j) (Finset.mem_range_succ_iff.mpr hL)
    have hm := mul_le_mul_of_nonneg_left he hfac
    dsimp [C]
    linarith
  have hb' := hb.enlarge hDC
  have hs := budgetedGeneratorExpansion_scale_bound hKΩ hb' hx ht ht1 hr hr1
    (exists_short_frame hstep (hKΩ hx)) hB
  have he := shortDerivatives_eq_relative_mul hΩ hX hstep B
    (budgetedGeneratorExpansion_forget hf)
    (f := frameDet (shortField w X) B')
    (fun _y hy => frameDet_eq_coordinateDet_mul _ B B' hy.2) L
    ⟨hKΩ hx, suboptimal_frame_ne_zero ht hr (exists_short_frame hstep (hKΩ hx)) hB⟩
  rw [he, abs_mul]
  exact mul_le_mul_of_nonneg_right hs (abs_nonneg _)

end RothschildStein.G4

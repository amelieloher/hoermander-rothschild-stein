-- Copyright (c) 2026 Scott Armstrong and Amélie Loher. All rights reserved.
-- Released under Apache 2.0 license as described in the file LICENSE.
module

public import RothschildStein.G4.UniversalSelectedDeterminantDerivativeBounds
public import RothschildStein.G4.WeightedControlProducts

@[expose] public section
set_option autoImplicit false
set_option relaxedAutoImplicit false
noncomputable section
open Set
open scoped BigOperators

namespace RothschildStein.G4

/-- All initial Taylor derivatives of the selected determinant
have universal weighted-control bounds. C is chosen before the actual
fields, frame, center, controls and spatial sets. -/
theorem exists_initial_frameDet_flow_derivative_bound (k n s l : ℕ)
    (w : Fin (k + 1) → ℕ+) (M Δ : ℝ) (hM : 0 ≤ M) (hΔ : 0 < Δ) :
    ∃ C : ℝ, 0 < C ∧ ∀ (Ω K : Set (Fin n → ℝ)), IsOpen Ω → K ⊆ Ω →
      ∀ (X : Fin (k + 1) → (Fin n → ℝ) → (Fin n → ℝ)),
      (∀ i, ContDiffOn ℝ (⊤ : ℕ∞) (X i) Ω) → bracketStepOn Ω w X s →
      (∀ i, HasJetBound Ω K (X i) (l + 2 * s) M) →
      (∀ x ∈ K, Δ ^ 2 ≤ determinantSquareSum (shortField (s := s) w X) x) →
      ∀ (B : Fin n → ShortWord w s) (j : ℕ), j ≤ l → ∀ x ∈ K,
      ∀ t r e : ℝ, 0 < t → t ≤ 1 → 0 < r → r ≤ 1 → 0 ≤ e → e ≤ 1 →
      IsSuboptimal (shortField w X) (shortWeight w) B x t r →
      ∀ a : ShortWord w s → ℝ, (∀ I, |a I| ≤ (e * r) ^ (shortWeight w I : ℕ)) →
      |fieldIterates (fun y => ∑ I, a I • shortField w X I y) j
        (frameDet (shortField w X) B) x| ≤
        (Fintype.card (ShortWord w s) : ℝ) ^ j * C * t⁻¹ ^ j * e ^ j *
          |frameDet (shortField w X) B x| := by
  obtain ⟨C, hC, hc⟩ := exists_universal_selected_determinant_derivative_bound k n s l w M Δ hM hΔ
  refine ⟨C, hC, ?_⟩
  intro Ω K hΩ hKΩ X hX hstep hjets hdet B j hj x hx t r e ht ht1 hr hr1 he he1 hB a ha
  have hZ := shortField_contDiffOn (w := w) (s := s) hΩ hX
  apply fieldIterates_weighted_control_bound hΩ hZ (frameDet_contDiffOn hZ B)
    (shortWeight w) a j (hKΩ hx) he he1 hr ht hC.le (abs_nonneg _) ha
  intro L hL
  simpa only [hL] using hc Ω K hΩ hKΩ X hX hstep hjets hdet B L
    (hL.trans_le hj) x hx t r ht ht1 hr hr1 hB

end RothschildStein.G4

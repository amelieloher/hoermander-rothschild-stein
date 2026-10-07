-- Copyright (c) 2026 Scott Armstrong and Amélie Loher. All rights reserved.
-- Released under Apache 2.0 license as described in the file LICENSE.
module

public import RothschildStein.G4.FiniteBinaryWords
public import RothschildStein.G4.BracketReduction

@[expose] public section
set_option autoImplicit false
set_option relaxedAutoImplicit false
noncomputable section
open Set Hormander.C

namespace RothschildStein.G4

/-- Uniform finite jets of the full entire-bracket reduction.
The constant is chosen before every actual binary expression, vector
field and spatial set; it depends on the numerical maximum word weight. -/
theorem exists_binaryReductionCoefficient_jet_bound (k n s h L : ℕ)
    (w : Fin (k + 1) → ℕ+) (hsL : s ≤ L) (M Δ : ℝ) (hM : 0 ≤ M) (hΔ : 0 < Δ) :
    ∃ C : ℝ, 0 < C ∧ ∀ (Ω K : Set (Fin n → ℝ)), IsOpen Ω → K ⊆ Ω →
      ∀ (X : Fin (k + 1) → (Fin n → ℝ) → (Fin n → ℝ)),
      (∀ i, ContDiffOn ℝ (⊤ : ℕ∞) (X i) Ω) → bracketStepOn Ω w X s →
      (∀ i, HasJetBound Ω K (X i) (h + L) M) →
      (∀ x ∈ K, Δ ^ 2 ≤ determinantSquareSum (shortField (s := s) w X) x) →
      ∀ u : Hormander.Interface.LieWord k, G1.binaryWeight w u ≤ L →
      ∀ J : ShortWord w s, HasJetBound Ω K (binaryReductionCoefficient w X u J) h C := by
  obtain ⟨A, hA, hword⟩ := exists_short_word_reduction_jet_bound (k + 1) n s h L w hsL M Δ hM hΔ
  refine ⟨binaryMassBudget k L * A, mul_pos (binaryMassBudget_pos k L) hA, ?_⟩
  intro Ω K hΩ hKΩ X hX hstep hjets hdet u hu J
  have hlength : ∀ z ∈ binaryExpansion u, (G1.nestedLetters z.2).length ≤ L := by
    intro z hz
    have he := wordLength_le_wordWeight w (G1.nestedLetters z.2)
    change _ ≤ G1.nestedWeight w z.2 at he
    rw [G1.binaryExpansion_weight w u z hz] at he
    exact he.trans hu
  have hb := combinationReductionCoefficient_jet_bound hΩ hKΩ w X hX hstep
    (binaryExpansion u) J (fun z hz =>
      hword Ω K hΩ hKΩ X hX hstep hjets hdet _ (hlength z hz) J)
  exact hb.enlarge (mul_le_mul_of_nonneg_right (combinationMass_le_binaryMassBudget w u hu) hA.le)

end RothschildStein.G4

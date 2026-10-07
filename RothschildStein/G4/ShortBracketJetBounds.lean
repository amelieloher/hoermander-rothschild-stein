-- Copyright (c) 2026 Scott Armstrong and Amélie Loher. All rights reserved.
-- Released under Apache 2.0 license as described in the file LICENSE.
module

public import RothschildStein.G4.CombinationJetBounds
public import RothschildStein.G4.ShortBracketReduction

@[expose] public section
set_option autoImplicit false
set_option relaxedAutoImplicit false
noncomputable section
open Set Hormander.C
open scoped BigOperators

namespace RothschildStein.G4

/-- A finite universal Jacobi coefficient budget for pairs of
short words. It depends on their fixed combinatorial carrier only. -/
def shortBracketMassBudget {k s : ℕ} (w : Fin (k + 1) → ℕ+) : ℝ :=
  1 + ∑ L : ShortWord w s, ∑ J : ShortWord w s,
    combinationMass (binaryExpansion (.bracket (shortBinaryWord w L) (shortBinaryWord w J)))

/-- The Jacobi coefficient budget dominates one. -/
theorem one_le_shortBracketMassBudget {k s : ℕ} (w : Fin (k + 1) → ℕ+) :
    1 ≤ shortBracketMassBudget (s := s) w := by
  have hn : 0 ≤ ∑ L : ShortWord w s, ∑ J : ShortWord w s,
    combinationMass (binaryExpansion (.bracket (shortBinaryWord w L) (shortBinaryWord w J))) :=
      Finset.sum_nonneg (fun L _ => Finset.sum_nonneg (fun J _ => combinationMass_nonneg _))
  unfold shortBracketMassBudget
  linarith

/-- Actual short-bracket reduction coefficients have a universal
finite jet bound, chosen before the domain, actual fields and compact
buffer. Only generator jets through h+2s enter. -/
theorem exists_shortBracketCoefficient_jet_bound (k n s h : ℕ)
    (w : Fin (k + 1) → ℕ+) (M Δ : ℝ) (hM : 0 ≤ M) (hΔ : 0 < Δ) :
    ∃ A : ℝ, 0 < A ∧ ∀ (Ω K₀ : Set (Fin n → ℝ)), IsOpen Ω → K₀ ⊆ Ω →
      ∀ (X : Fin (k + 1) → (Fin n → ℝ) → (Fin n → ℝ)),
      (∀ i, ContDiffOn ℝ (⊤ : ℕ∞) (X i) Ω) → bracketStepOn Ω w X s →
      (∀ i, HasJetBound Ω K₀ (X i) (h + 2 * s) M) →
      (∀ x ∈ K₀, Δ ^ 2 ≤ determinantSquareSum (shortField (s := s) w X) x) →
      ∀ L J K : ShortWord w s, HasJetBound Ω K₀ (shortBracketCoefficient w X L J K) h A := by
  classical
  obtain ⟨C, hC, hc⟩ := exists_short_word_reduction_jet_bound (k + 1) n s h (2 * s) w
    (by omega) M Δ hM hΔ
  let D := shortBracketMassBudget (s := s) w
  have hD : 0 < D := zero_lt_one.trans_le (one_le_shortBracketMassBudget w)
  refine ⟨D * C, mul_pos hD hC, ?_⟩
  intro Ω K₀ hΩ hKΩ X hX hstep hjets hdet L J K
  let F := binaryExpansion (.bracket (shortBinaryWord w L) (shortBinaryWord w J))
  have hF : ∀ z ∈ F, (G1.nestedLetters z.2).length ≤ 2 * s := by
    intro z hz
    have hw := G1.binaryExpansion_weight w (.bracket (shortBinaryWord w L) (shortBinaryWord w J)) z hz
    have hl := wordLength_le_wordWeight w (G1.nestedLetters z.2)
    change _ ≤ G1.nestedWeight w z.2 at hl
    rw [hw] at hl
    change _ ≤ G1.binaryWeight w (shortBinaryWord w L) + G1.binaryWeight w (shortBinaryWord w J) at hl
    rw [shortBinaryWord_weight, shortBinaryWord_weight] at hl
    have hL := ((mem_shortWordFamily_iff w L.val).mp L.property).2
    have hJ := ((mem_shortWordFamily_iff w J.val).mp J.property).2
    change (shortWeight w L : ℕ) ≤ s at hL
    change (shortWeight w J : ℕ) ≤ s at hJ
    omega
  have hb := combinationReductionCoefficient_jet_bound hΩ hKΩ w X hX hstep F K
    (fun z hz => hc Ω K₀ hΩ hKΩ X hX hstep hjets hdet _ (hF z hz) K)
  have h₁ : combinationMass F ≤ ∑ J' : ShortWord w s,
      combinationMass (binaryExpansion (.bracket (shortBinaryWord w L) (shortBinaryWord w J'))) :=
    Finset.single_le_sum (fun J' _ => combinationMass_nonneg
      (binaryExpansion (.bracket (shortBinaryWord w L) (shortBinaryWord w J'))))
      (Finset.mem_univ J)
  have h₂ : (∑ J' : ShortWord w s,
      combinationMass (binaryExpansion (.bracket (shortBinaryWord w L) (shortBinaryWord w J')))) ≤
      ∑ L' : ShortWord w s, ∑ J' : ShortWord w s,
        combinationMass (binaryExpansion (.bracket (shortBinaryWord w L') (shortBinaryWord w J'))) :=
    Finset.single_le_sum (fun L' _ => Finset.sum_nonneg (fun J' _ =>
      combinationMass_nonneg (binaryExpansion (.bracket (shortBinaryWord w L') (shortBinaryWord w J')))))
      (Finset.mem_univ L)
  have hm : combinationMass F ≤ D := (h₁.trans h₂).trans (by dsimp [D, shortBracketMassBudget]; linarith)
  exact hb.enlarge (mul_le_mul_of_nonneg_right hm hC.le)

end RothschildStein.G4

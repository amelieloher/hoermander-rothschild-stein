-- Copyright (c) 2026 Scott Armstrong and Amélie Loher. All rights reserved.
-- Released under Apache 2.0 license as described in the file LICENSE.
module

public import RothschildStein.G4.BinaryReductionJetBounds
public import RothschildStein.G4.PersistentCoefficientBounds

@[expose] public section
set_option autoImplicit false
set_option relaxedAutoImplicit false
noncomputable section
open Set
open scoped BigOperators

namespace RothschildStein.G4

/-- The full entire-bracket Cramer estimate has a numerical
constant uniform over every binary expression below the weight cutoff.
The determinant persistence constant is used linearly, so substituting
D t⁻ⁿ introduces exactly n inverse-suboptimality factors. -/
theorem exists_uniform_binary_frameCoefficient_bound (k n s L : ℕ)
    (w : Fin (k + 1) → ℕ+) (hsL : s ≤ L) (M Δ : ℝ) (hM : 0 ≤ M) (hΔ : 0 < Δ) :
    ∃ C : ℝ, 0 < C ∧ ∀ (Ω K : Set (Fin n → ℝ)), IsOpen Ω → K ⊆ Ω →
      ∀ (X : Fin (k + 1) → (Fin n → ℝ) → (Fin n → ℝ)),
      (∀ i, ContDiffOn ℝ (⊤ : ℕ∞) (X i) Ω) → bracketStepOn Ω w X s →
      (∀ i, HasJetBound Ω K (X i) L M) →
      (∀ y ∈ K, Δ ^ 2 ≤ determinantSquareSum (shortField (s := s) w X) y) →
      ∀ u : Hormander.Interface.LieWord k, G1.binaryWeight w u ≤ L →
      ∀ (B : Fin n → ShortWord w s) (i : Fin n) (x y : Fin n → ℝ), y ∈ K →
      ∀ r D : ℝ, 0 < r → r ≤ 1 → 0 ≤ D → frameDet (shortField w X) B x ≠ 0 →
      (|frameDet (shortField w X) B x| / 2 ≤ |frameDet (shortField w X) B y|) →
      (∀ B' : Fin n → ShortWord w s, |frameDet (shortField w X) B' y| ≤
        D * r ^ (frameWeight (shortWeight w) B - frameWeight (shortWeight w) B') *
          |frameDet (shortField w X) B x|) →
      |frameCoefficient (shortField w X) B (Hormander.lieWordEval X u) i y| ≤
        C * D * r ^ (((shortWeight w (B i) : ℕ) : ℤ) - (G1.binaryWeight w u : ℤ)) := by
  obtain ⟨A, hA, hcoeff⟩ := exists_binaryReductionCoefficient_jet_bound k n s 0 L w hsL M Δ hM hΔ
  let C := 1 + 2 * (Fintype.card (ShortWord w s) : ℝ) * A
  have hCA : 0 ≤ 2 * (Fintype.card (ShortWord w s) : ℝ) * A := by positivity
  refine ⟨C, by dsimp [C]; linarith, ?_⟩
  intro Ω K hΩ hKΩ X hX hstep hjets hdet u hu B i x y hy r D hr hr1 hD hBx hhalf hpersist
  have hc : ∑ J : ShortWord w s, |binaryReductionCoefficient w X u J y| ≤
      (Fintype.card (ShortWord w s) : ℝ) * A := by
    calc
      _ ≤ ∑ _ : ShortWord w s, A := Finset.sum_le_sum (fun J _ => by
        have hb := hcoeff Ω K hΩ hKΩ X hX hstep
          (fun i => by simpa only [zero_add] using hjets i) hdet u hu J
        simpa using hb 0 (Nat.zero_le _) y hy)
      _ = _ := by simp only [Finset.sum_const, Finset.card_univ, nsmul_eq_mul]
  have hb := binary_frameCoefficient_le_of_determinant_bounds hΩ hX hstep u B i (hKΩ hy)
    hr hr1 hD hc hBx hhalf hpersist
  apply hb.trans
  have he : 2 * (Fintype.card (ShortWord w s) : ℝ) * A ≤ C := by dsimp [C]; linarith
  have hm := mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_right he hD)
    (zpow_nonneg hr.le (((shortWeight w (B i) : ℕ) : ℤ) - (G1.binaryWeight w u : ℤ)))
  convert hm using 1
  dsimp [shortWeight]
  ring

end RothschildStein.G4

-- Copyright (c) 2026 Scott Armstrong and Amélie Loher. All rights reserved.
-- Released under Apache 2.0 license as described in the file LICENSE.
module
public import RothschildStein.G3.FieldPowerBounds
public import RothschildStein.S.ClassicalWords
@[expose] public section
noncomputable section
open Set TopologicalSpace
namespace RothschildStein.G3

/-- Every ordered word has a quantitative finite jet bound,
losing exactly its ordinary length in function jets (BB pp. 410–420). -/
theorem norm_wordDerivative_jet_le {a N R : ℕ} (Ω : Opens (Fin N → ℝ))
    (X : Fin a → (Fin N → ℝ) → (Fin N → ℝ))
    (hX : ∀ i, ContDiffOn ℝ (⊤ : ℕ∞) (X i) Ω)
    (f : (Fin N → ℝ) → ℝ) (hf : ContDiffOn ℝ (⊤ : ℕ∞) f Ω)
    {x : Fin N → ℝ} (hx : x ∈ Ω) {B F : ℝ} (hB : 0 ≤ B)
    (hXjet : ∀ i, ∀ j ≤ R, ‖iteratedFDeriv ℝ j (X i) x‖ ≤ B)
    (hfjet : ∀ j ≤ R, ‖iteratedFDeriv ℝ j f x‖ ≤ F)
    (I : List (Fin a)) (n : ℕ) (hn : n + I.length ≤ R) :
    ‖iteratedFDeriv ℝ n (wordDerivative X I f) x‖ ≤ (2 ^ R * B) ^ I.length * F := by
  have hF : 0 ≤ F := (norm_nonneg _).trans (hfjet 0 (Nat.zero_le R))
  induction I generalizing n with
  | nil => simpa only [wordDerivative, List.length_nil, pow_zero, one_mul] using hfjet n (by omega)
  | cons i I ih =>
    change ‖iteratedFDeriv ℝ n (fieldDerivative (X i) (wordDerivative X I f)) x‖ ≤ _
    have hfj : ∀ j ≤ n + 1, ‖iteratedFDeriv ℝ j (wordDerivative X I f) x‖ ≤
        (2 ^ R * B) ^ I.length * F := fun j hj => ih j (by simp only [List.length_cons] at hn; omega)
    have hb := norm_fieldDerivative_jet_le (R := n + 1) Ω (X i) (hX i) (wordDerivative X I f)
      (S.contDiffOn_wordDerivative Ω X hX I f hf) hx le_rfl
      (fun j hj => hXjet i j (by simp only [List.length_cons] at hn; omega)) hfj
    apply hb.trans
    calc
      2 ^ n * ((2 ^ R * B) ^ I.length * F) * B ≤
          2 ^ R * ((2 ^ R * B) ^ I.length * F) * B := by
        apply mul_le_mul_of_nonneg_right _ hB
        apply mul_le_mul_of_nonneg_right _ (mul_nonneg (pow_nonneg (mul_nonneg (by positivity) hB) _) hF)
        exact pow_le_pow_right₀ (by norm_num : (1 : ℝ) ≤ 2) (by omega : n ≤ R)
      _ = (2 ^ R * B) ^ (i :: I).length * F := by
        rw [List.length_cons, pow_succ]
        ring
end RothschildStein.G3

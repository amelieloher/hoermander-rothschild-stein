-- Copyright (c) 2026 Scott Armstrong and Amélie Loher. All rights reserved.
-- Released under Apache 2.0 license as described in the file LICENSE.
module
public import RothschildStein.G3.BracketUniformJets
@[expose] public section
noncomputable section
open Set TopologicalSpace
namespace RothschildStein.G3

/-- An ordinary length-l nested bracket loses l-1 primitive
coefficient jets. Its jet bound is polynomial in the primitive coefficient
norm; weighted drift letters do not alter this jet-loss count (BB pp. 413–420). -/
theorem norm_wordBracket_jet_le {a N R : ℕ} (Ω : Opens (Fin N → ℝ))
    (X : Fin a → (Fin N → ℝ) → (Fin N → ℝ))
    (hX : ∀ i, ContDiffOn ℝ (⊤ : ℕ∞) (X i) Ω)
    {x : Fin N → ℝ} (hx : x ∈ Ω) {B : ℝ} (hB : 0 ≤ B)
    (hXjet : ∀ i, ∀ j ≤ R, ‖iteratedFDeriv ℝ j (X i) x‖ ≤ B)
    (I : List (Fin a)) (hne : I ≠ []) (n : ℕ) (hn : n + I.length ≤ R + 1) :
    ‖iteratedFDeriv ℝ n (wordBracket X I) x‖ ≤
      (2 ^ (R + 1)) ^ (I.length - 1) * B ^ I.length := by
  induction I generalizing n with
  | nil => exact False.elim (hne rfl)
  | cons i I ih =>
    cases I with
    | nil =>
      simpa only [wordBracket, List.length_singleton, Nat.sub_self, pow_zero, one_mul, pow_one]
        using hXjet i n (by simp only [List.length_singleton] at hn; omega)
    | cons j I =>
      have htail : ∀ l ≤ n + 1, ‖iteratedFDeriv ℝ l (wordBracket X (j :: I)) x‖ ≤
          (2 ^ (R + 1)) ^ ((j :: I).length - 1) * B ^ (j :: I).length := by
        intro l hl
        exact ih (List.cons_ne_nil j I) l (by simp only [List.length_cons] at hn ⊢; omega)
      have hh := norm_bracket_jet_le (R := n + 1) Ω (X i) (wordBracket X (j :: I))
        (hX i) (G1.wordBracket_contDiffOn Ω.isOpen X hX (j :: I)) hx le_rfl
        (fun l hl => hXjet i l (by simp only [List.length_cons] at hn; omega)) htail
      change ‖iteratedFDeriv ℝ n (VectorField.lieBracket ℝ (X i) (wordBracket X (j :: I))) x‖ ≤ _
      apply hh.trans
      calc
        _ ≤ 2 ^ (R + 1) * B *
            ((2 ^ (R + 1)) ^ ((j :: I).length - 1) * B ^ (j :: I).length) := by
          apply mul_le_mul_of_nonneg_right _ (mul_nonneg (by positivity) (pow_nonneg hB _))
          apply mul_le_mul_of_nonneg_right _ hB
          exact pow_le_pow_right₀ (by norm_num : (1 : ℝ) ≤ 2)
            (by simp only [List.length_cons] at hn; omega)
        _ = _ := by
          simp only [List.length_cons, Nat.add_sub_cancel]
          rw [pow_succ (2 ^ (R + 1) : ℝ) I.length, pow_succ B (I.length + 1)]
          ring
end RothschildStein.G3

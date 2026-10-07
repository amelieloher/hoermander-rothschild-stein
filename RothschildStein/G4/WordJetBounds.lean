-- Copyright (c) 2026 Scott Armstrong and Amélie Loher. All rights reserved.
-- Released under Apache 2.0 license as described in the file LICENSE.
module

public import RothschildStein.G4.BracketJetBounds

@[expose] public section
set_option autoImplicit false
set_option relaxedAutoImplicit false
noncomputable section
open Set

namespace RothschildStein.G4

/-- A universal base for the finite coefficient-jet polynomial
bound, depending only on dimension, jet order, word length and input budget. -/
def wordJetBase (n h l : ℕ) (M : ℝ) : ℝ :=
  1 + M + 2 * ‖(ContinuousLinearMap.apply ℝ (Fin n → ℝ) :
    (Fin n → ℝ) →L[ℝ] ((Fin n → ℝ) →L[ℝ] (Fin n → ℝ)) →L[ℝ] (Fin n → ℝ))‖ * 2 ^ (h + l) * M

/-- The universal base is nonnegative and dominates the input budget. -/
theorem wordJetBase_nonneg_and_le {n h l : ℕ} {M : ℝ} (hM : 0 ≤ M) :
    0 ≤ wordJetBase n h l M ∧ M ≤ wordJetBase n h l M := by
  have hB : 0 ≤ ‖(ContinuousLinearMap.apply ℝ (Fin n → ℝ) :
    (Fin n → ℝ) →L[ℝ] ((Fin n → ℝ) →L[ℝ] (Fin n → ℝ)) →L[ℝ] (Fin n → ℝ))‖ :=
    ContinuousLinearMap.opNorm_nonneg _
  have hh : 0 ≤ 2 * ‖(ContinuousLinearMap.apply ℝ (Fin n → ℝ) :
    (Fin n → ℝ) →L[ℝ] ((Fin n → ℝ) →L[ℝ] (Fin n → ℝ)) →L[ℝ] (Fin n → ℝ))‖ * 2 ^ (h + l) * M := by positivity
  dsimp [wordJetBase]
  constructor <;> linarith

/-- Actual word-bracket jets have a universal finite coefficient
budget. Only generator jets through order `h + length(I)` are used
(BB Lemma 9.31, pp. 422–423). -/
theorem wordBracket_jet_bound {m n : ℕ} {Ω K : Set (Fin n → ℝ)}
    (hΩ : IsOpen Ω) (hKΩ : K ⊆ Ω)
    (X : Fin m → (Fin n → ℝ) → (Fin n → ℝ))
    (hX : ∀ i, ContDiffOn ℝ (⊤ : ℕ∞) (X i) Ω)
    (I : List (Fin m)) {h : ℕ} {M : ℝ} (hM : 0 ≤ M)
    (hjets : ∀ i, HasJetBound Ω K (X i) (h + I.length) M) :
    HasJetBound Ω K (wordBracket X I) h (wordJetBase n h I.length M ^ I.length) := by
  induction I generalizing h with
  | nil =>
    intro j hj x hx
    cases j with
    | zero => simp [wordBracket]
    | succ j => simp [wordBracket]
  | cons i I ih =>
    cases I with
    | nil =>
      intro j hj x hx
      have hh := hjets i j (hj.trans (Nat.le_add_right h 1)) x hx
      exact hh.trans (by simpa only [List.length_singleton, pow_one] using
        (wordJetBase_nonneg_and_le (n := n) (h := h) (l := 1) hM).2)
    | cons j I =>
      have htailjets : ∀ i, HasJetBound Ω K (X i) ((h + 1) + (j :: I).length) M := by
        intro i
        convert hjets i using 1
        simp only [List.length_cons]
        omega
      have htail := ih (h := h + 1) htailjets
      have hfirst : HasJetBound Ω K (X i) (h + 1) M :=
        (hjets i).mono (by simp only [List.length_cons]; omega)
      have hh := hfirst.lieBracket hΩ hKΩ (hX i)
        (G1.wordBracket_contDiffOn hΩ X hX (j :: I)) hM
        (pow_nonneg (wordJetBase_nonneg_and_le hM).1 _) htail
      have hbase : wordJetBase n (h + 1) (j :: I).length M =
          wordJetBase n h (i :: j :: I).length M := by
        unfold wordJetBase
        have he : (h + 1) + (j :: I).length = h + (i :: j :: I).length := by
          simp only [List.length_cons]
          omega
        rw [he]
      have hfactor : 2 * ‖(ContinuousLinearMap.apply ℝ (Fin n → ℝ) :
          (Fin n → ℝ) →L[ℝ] ((Fin n → ℝ) →L[ℝ] (Fin n → ℝ)) →L[ℝ] (Fin n → ℝ))‖ * 2 ^ h * M ≤
          wordJetBase n h (i :: j :: I).length M := by
        have hBn : 0 ≤ ‖(ContinuousLinearMap.apply ℝ (Fin n → ℝ) :
          (Fin n → ℝ) →L[ℝ] ((Fin n → ℝ) →L[ℝ] (Fin n → ℝ)) →L[ℝ] (Fin n → ℝ))‖ :=
          ContinuousLinearMap.opNorm_nonneg _
        have hp : (2 : ℝ) ^ h ≤ 2 ^ (h + (i :: j :: I).length) :=
          pow_le_pow_right₀ (by norm_num) (Nat.le_add_right _ _)
        have hm := mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_left hp
          (mul_nonneg (by norm_num : (0 : ℝ) ≤ 2) hBn)) hM
        dsimp [wordJetBase]
        simp only [List.length_cons] at hm
        linarith
      intro r hr x hx
      have hd := hh r hr x hx
      rw [hbase] at hd
      exact hd.trans (by
        change _ ≤ wordJetBase n h (i :: j :: I).length M ^ (i :: j :: I).length
        have hp := mul_le_mul_of_nonneg_right hfactor
          (pow_nonneg (wordJetBase_nonneg_and_le (n := n) (h := h)
            (l := (i :: j :: I).length) hM).1 (j :: I).length)
        simpa only [List.length_cons, pow_succ, mul_assoc, mul_left_comm, mul_comm] using hp)

end RothschildStein.G4

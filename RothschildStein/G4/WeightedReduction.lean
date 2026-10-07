-- Copyright (c) 2026 Scott Armstrong and Amélie Loher. All rights reserved.
-- Released under Apache 2.0 license as described in the file LICENSE.
module

public import RothschildStein.G4.ShortFields
public import RothschildStein.G1.WeightedNormalization

@[expose] public section
set_option autoImplicit false
set_option relaxedAutoImplicit false
noncomputable section
open Set Hormander.C
open scoped BigOperators

namespace RothschildStein.G4

/-- Keep short words unchanged; only genuinely long words
use the global squared-determinant reduction. -/
def wordReductionCoefficient {m n s : ℕ} (w : Fin m → ℕ+)
    (X : Fin m → (Fin n → ℝ) → (Fin n → ℝ)) (K : List (Fin m))
    (J : ShortWord w s) (x : Fin n → ℝ) : ℝ :=
  if K = [] then 0 else
  if K ∈ shortWordFamily w s then (if J.val = K then 1 else 0) else
    reductionCoefficient (shortField w X) (wordBracket X K) J x

/-- The selected reduction coefficients are smooth on the
original spanning domain (BB Lemma 9.31, pp. 422–423). -/
theorem wordReductionCoefficient_contDiffOn {m n s : ℕ} {Ω : Set (Fin n → ℝ)}
    (hΩ : IsOpen Ω) {w : Fin m → ℕ+}
    {X : Fin m → (Fin n → ℝ) → (Fin n → ℝ)}
    (hX : ∀ i, ContDiffOn ℝ (⊤ : ℕ∞) (X i) Ω)
    (hstep : bracketStepOn Ω w X s) (K : List (Fin m)) (J : ShortWord w s) :
    ContDiffOn ℝ (⊤ : ℕ∞) (wordReductionCoefficient w X K J) Ω := by
  classical
  unfold wordReductionCoefficient
  split_ifs
  · exact contDiffOn_const
  · exact contDiffOn_const
  · exact contDiffOn_const
  · exact reductionCoefficient_contDiffOn (shortField_contDiffOn hΩ hX)
      (G1.wordBracket_contDiffOn hΩ X hX K) (fun x hx => exists_short_frame hstep hx) J

/-- This reduction represents the actual field, with identity
coefficients for short words (BB Lemma 9.31, pp. 422–423). -/
theorem word_reduction_representation {m n s : ℕ} {Ω : Set (Fin n → ℝ)}
    {w : Fin m → ℕ+} {X : Fin m → (Fin n → ℝ) → (Fin n → ℝ)}
    (hstep : bracketStepOn Ω w X s) (K : List (Fin m))
    {x : Fin n → ℝ} (hx : x ∈ Ω) :
    wordBracket X K x = ∑ J : ShortWord w s, wordReductionCoefficient w X K J x • shortField w X J x := by
  classical
  by_cases hnil : K = []
  · subst K
    simp [wordReductionCoefficient, wordBracket]
  by_cases hshort : K ∈ shortWordFamily w s
  · let J₀ : ShortWord w s := ⟨K, hshort⟩
    have heq : ∀ J : ShortWord w s, (J.val = K) ↔ J = J₀ :=
      fun J => ⟨fun h => Subtype.ext h, fun h => congrArg Subtype.val h⟩
    simp [wordReductionCoefficient, hnil, hshort, heq, J₀, shortField]
  · simpa only [wordReductionCoefficient, ite_eq_right hnil, ite_eq_right hshort] using
      global_reduction_representation (shortField (s := s) w X) (wordBracket X K)
        (exists_short_frame hstep hx)

/-- A coefficient vanishes unless the short word's weight
is at most the original word's weight. This is the exact restriction needed
by the nested-bracket estimate (BB Proposition 9.32(a), p. 424). -/
theorem wordReductionCoefficient_eq_zero_of_weight_lt {m n s : ℕ}
    (w : Fin m → ℕ+) (X : Fin m → (Fin n → ℝ) → (Fin n → ℝ))
    (K : List (Fin m)) (J : ShortWord w s)
    (hweight : wordWeight w K < wordWeight w J.val) :
    wordReductionCoefficient w X K J = 0 := by
  classical
  funext x
  unfold wordReductionCoefficient
  by_cases hnil : K = []
  · simp only [ite_eq_left hnil, Pi.zero_apply]
  have hshort : K ∈ shortWordFamily w s := (mem_shortWordFamily_iff w K).mpr
    ⟨hnil, hweight.le.trans ((mem_shortWordFamily_iff w J.val).mp J.property).2⟩
  have hne : J.val ≠ K := fun h => by rw [h] at hweight; exact (lt_irrefl _) hweight
  simp only [ite_eq_right hnil, ite_eq_left hshort, ite_eq_right hne, Pi.zero_apply]

/-- Reduce a constant Jacobi combination only after its entire
bracket expansion. Coefficients are finite integer sums of word reductions. -/
def combinationReductionCoefficient {k n s : ℕ} (w : Fin (k + 1) → ℕ+)
    (X : Fin (k + 1) → (Fin n → ℝ) → (Fin n → ℝ)) :
    WordCombination k → ShortWord w s → (Fin n → ℝ) → ℝ
  | [], _, _ => 0
  | (a, u) :: L, J, x => (a : ℝ) * wordReductionCoefficient w X (G1.nestedLetters u) J x +
      combinationReductionCoefficient w X L J x

/-- The combination reduction is smooth before using any local
frame ratio (BB Lemmas 9.30–9.31, pp. 422–423). -/
theorem combinationReductionCoefficient_contDiffOn {k n s : ℕ}
    {Ω : Set (Fin n → ℝ)} (hΩ : IsOpen Ω) {w : Fin (k + 1) → ℕ+}
    {X : Fin (k + 1) → (Fin n → ℝ) → (Fin n → ℝ)}
    (hX : ∀ i, ContDiffOn ℝ (⊤ : ℕ∞) (X i) Ω)
    (hstep : bracketStepOn Ω w X s) (L : WordCombination k) (J : ShortWord w s) :
    ContDiffOn ℝ (⊤ : ℕ∞) (combinationReductionCoefficient w X L J) Ω := by
  induction L with
  | nil => exact contDiffOn_const
  | cons z L ih =>
    exact (contDiffOn_const.mul (wordReductionCoefficient_contDiffOn hΩ hX hstep _ J)).add ih

/-- Actual evaluation of the globally reduced Jacobi combination
(BB Lemmas 9.30–9.31, pp. 422–423). -/
theorem combination_reduction_representation {k n s : ℕ}
    {Ω : Set (Fin n → ℝ)} {w : Fin (k + 1) → ℕ+}
    {X : Fin (k + 1) → (Fin n → ℝ) → (Fin n → ℝ)}
    (hstep : bracketStepOn Ω w X s) (L : WordCombination k)
    {x : Fin n → ℝ} (hx : x ∈ Ω) :
    combinationEval X L x =
      ∑ J : ShortWord w s, combinationReductionCoefficient w X L J x • shortField w X J x := by
  induction L with
  | nil => simp [combinationEval, combinationReductionCoefficient]
  | cons z L ih =>
    rcases z with ⟨a, u⟩
    rw [combinationEval, G1.nestedEval_eq_wordBracket]
    dsimp only
    rw [word_reduction_representation hstep _ hx, ih]
    simp only [combinationReductionCoefficient, add_smul, Finset.sum_add_distrib,
      Finset.smul_sum, smul_smul]

/-- Weight preservation survives the entire global reduction
(BB Lemma 9.30, p. 422; nested-bracket reduction). -/
theorem combinationReductionCoefficient_eq_zero_of_weight_lt {k n s : ℕ}
    (w : Fin (k + 1) → ℕ+) (X : Fin (k + 1) → (Fin n → ℝ) → (Fin n → ℝ))
    (L : WordCombination k) {W : ℕ}
    (hL : ∀ z ∈ L, G1.nestedWeight w z.2 = W) (J : ShortWord w s)
    (hweight : W < wordWeight w J.val) : combinationReductionCoefficient w X L J = 0 := by
  induction L with
  | nil => rfl
  | cons z L ih =>
    have hz := hL z (List.mem_cons_self)
    have ht := ih (fun v hv => hL v (List.mem_cons_of_mem _ hv))
    have hw : wordWeight w (G1.nestedLetters z.2) < wordWeight w J.val := by
      change G1.nestedWeight w z.2 < _
      rw [hz]
      exact hweight
    funext x
    simp only [combinationReductionCoefficient,
      wordReductionCoefficient_eq_zero_of_weight_lt w X _ J hw, ht, Pi.zero_apply,
      mul_zero, add_zero]

end RothschildStein.G4

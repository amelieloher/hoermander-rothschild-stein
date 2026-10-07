-- Copyright (c) 2026 Scott Armstrong and Amélie Loher. All rights reserved.
-- Released under Apache 2.0 license as described in the file LICENSE.
module

public import RothschildStein.G4.FiniteWordReductionBounds
public import RothschildStein.G4.WeightedReduction
public import RothschildStein.G4.AdditiveJetBounds

@[expose] public section
set_option autoImplicit false
set_option relaxedAutoImplicit false
noncomputable section
open Set

namespace RothschildStein.G4

/-- Positive letter weights dominate ordinary word length. -/
theorem wordLength_le_wordWeight {m : ℕ} (w : Fin m → ℕ+) (I : List (Fin m)) :
    I.length ≤ wordWeight w I := by
  classical
  rcases Classical.em (I = []) with he | he
  · subst I
    simp [wordWeight]
  clear he
  induction I with
  | nil => simp [wordWeight]
  | cons i I ih =>
    have hi : 1 ≤ (w i : ℕ) := (w i).pos
    simp only [List.length_cons, wordWeight, List.map_cons, List.sum_cons] at *
    omega

/-- Actual short coefficients, including the identity branch,
have a universal finite-jet bound. The fixed word carrier and maximum
word length are chosen before all spatial data and vector fields. -/
theorem exists_short_word_reduction_jet_bound (m n s h L : ℕ)
    (w : Fin m → ℕ+) (hsL : s ≤ L) (M Δ : ℝ) (hM : 0 ≤ M) (hΔ : 0 < Δ) :
    ∃ C : ℝ, 0 < C ∧ ∀ (Ω K₀ : Set (Fin n → ℝ)), IsOpen Ω → K₀ ⊆ Ω →
      ∀ (X : Fin m → (Fin n → ℝ) → (Fin n → ℝ)),
      (∀ i, ContDiffOn ℝ (⊤ : ℕ∞) (X i) Ω) → bracketStepOn Ω w X s →
      (∀ i, HasJetBound Ω K₀ (X i) (h + L) M) →
      (∀ x ∈ K₀, Δ ^ 2 ≤ determinantSquareSum (shortField (s := s) w X) x) →
      ∀ I : List (Fin m), I.length ≤ L → ∀ J : ShortWord w s,
        HasJetBound Ω K₀ (wordReductionCoefficient w X I J) h C := by
  classical
  obtain ⟨C, hC, hb⟩ := exists_finite_word_reduction_jet_bound (ShortWord w s) m n h L M Δ hM hΔ
  let D := max 1 C
  have hD : 0 < D := zero_lt_one.trans_le (le_max_left _ _)
  refine ⟨D, hD, ?_⟩
  intro Ω K₀ hΩ hKΩ X hX hstep hjets hdet I hI J
  by_cases hnil : I = []
  · have he : wordReductionCoefficient w X I J = fun _ => 0 := by
      funext x
      simp only [wordReductionCoefficient, ite_eq_left hnil]
    rw [he]
    exact (const_hasJetBound Ω K₀ h 0).enlarge (by simpa using hD.le)
  by_cases hshort : I ∈ shortWordFamily w s
  · have he : wordReductionCoefficient w X I J = fun _ => if J.val = I then 1 else 0 := by
      funext x
      simp only [wordReductionCoefficient, ite_eq_right hnil, ite_eq_left hshort]
    rw [he]
    split_ifs
    · exact (const_hasJetBound Ω K₀ h 1).enlarge (by simpa only [abs_one] using (show (1 : ℝ) ≤ D from le_max_left _ _))
    · exact (const_hasJetBound Ω K₀ h 0).enlarge (by simpa using hD.le)
  · have he : wordReductionCoefficient w X I J =
        reductionCoefficient (shortField w X) (wordBracket X I) J := by
      funext x
      simp only [wordReductionCoefficient, ite_eq_right hnil, ite_eq_right hshort]
    rw [he]
    have hW : ∀ A : ShortWord w s, A.val.length ≤ L := fun A =>
      (wordLength_le_wordWeight w A.val).trans
        (((mem_shortWordFamily_iff w A.val).mp A.property).2.trans hsL)
    exact (hb Ω K₀ hΩ hKΩ X hX hjets (fun A => A.val) I hW hI
      (fun x hx => ne_of_gt (determinantSquareSum_pos (exists_short_frame hstep hx)))
      hdet J).enlarge (le_max_right _ _)

end RothschildStein.G4

-- Copyright (c) 2026 Scott Armstrong and Amélie Loher. All rights reserved.
-- Released under Apache 2.0 license as described in the file LICENSE.
module

public import RothschildStein.G4.WordJetBounds

@[expose] public section
set_option autoImplicit false
set_option relaxedAutoImplicit false
noncomputable section
open Set

namespace RothschildStein.G4

/-- The universal word base is at least one. -/
theorem one_le_wordJetBase {n h l : ℕ} {M : ℝ} (hM : 0 ≤ M) :
    1 ≤ wordJetBase n h l M := by
  have hB : 0 ≤ ‖(ContinuousLinearMap.apply ℝ (Fin n → ℝ) :
    (Fin n → ℝ) →L[ℝ] ((Fin n → ℝ) →L[ℝ] (Fin n → ℝ)) →L[ℝ] (Fin n → ℝ))‖ :=
    ContinuousLinearMap.opNorm_nonneg _
  have hp : 0 ≤ 2 * ‖(ContinuousLinearMap.apply ℝ (Fin n → ℝ) :
    (Fin n → ℝ) →L[ℝ] ((Fin n → ℝ) →L[ℝ] (Fin n → ℝ)) →L[ℝ] (Fin n → ℝ))‖ *
      2 ^ (h + l) * M := by positivity
  unfold wordJetBase
  linarith

/-- Increasing the maximum word length increases the base. -/
theorem wordJetBase_mono_length {n h l L : ℕ} {M : ℝ}
    (hM : 0 ≤ M) (hl : l ≤ L) : wordJetBase n h l M ≤ wordJetBase n h L M := by
  have hB : 0 ≤ ‖(ContinuousLinearMap.apply ℝ (Fin n → ℝ) :
    (Fin n → ℝ) →L[ℝ] ((Fin n → ℝ) →L[ℝ] (Fin n → ℝ)) →L[ℝ] (Fin n → ℝ))‖ :=
    ContinuousLinearMap.opNorm_nonneg _
  have hp : (2 : ℝ) ^ (h + l) ≤ 2 ^ (h + L) :=
    pow_le_pow_right₀ (by norm_num) (Nat.add_le_add_left hl h)
  unfold wordJetBase
  gcongr

/-- A single universal jet budget controls every word of length
at most L, using generator jets only through h+L. -/
theorem wordBracket_jet_bound_uniform {m n : ℕ} {Ω K : Set (Fin n → ℝ)}
    (hΩ : IsOpen Ω) (hKΩ : K ⊆ Ω)
    (X : Fin m → (Fin n → ℝ) → (Fin n → ℝ))
    (hX : ∀ i, ContDiffOn ℝ (⊤ : ℕ∞) (X i) Ω)
    {h L : ℕ} {M : ℝ} (hM : 0 ≤ M)
    (hjets : ∀ i, HasJetBound Ω K (X i) (h + L) M)
    (I : List (Fin m)) (hIL : I.length ≤ L) :
    HasJetBound Ω K (wordBracket X I) h (wordJetBase n h L M ^ L) := by
  have hb := wordBracket_jet_bound hΩ hKΩ X hX I hM
    (fun i => (hjets i).mono (Nat.add_le_add_left hIL h))
  intro j hj x hx
  apply (hb j hj x hx).trans
  calc
    _ ≤ wordJetBase n h L M ^ I.length :=
      pow_le_pow_left₀ (wordJetBase_nonneg_and_le hM).1 (wordJetBase_mono_length hM hIL) _
    _ ≤ wordJetBase n h L M ^ L := pow_le_pow_right₀ (one_le_wordJetBase hM) hIL

end RothschildStein.G4

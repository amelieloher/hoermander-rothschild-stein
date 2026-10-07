-- Copyright (c) 2026 Scott Armstrong and Amélie Loher. All rights reserved.
-- Released under Apache 2.0 license as described in the file LICENSE.
module

public import RothschildStein.H3.DriftSecondWeakNorm

set_option autoImplicit false
set_option relaxedAutoImplicit false
set_option backward.isDefEq.respectTransparency false
@[expose] public section
noncomputable section
namespace RothschildStein.H3
open Set MeasureTheory TopologicalSpace
open scoped ENNReal
variable {n q : ℕ}

/-- Step 2: global second-word representatives control the complete
second norm on every patch, without requiring global first derivatives. -/
theorem driftSecondWeakENorm_local_bound_of_global_words
    (X : Fin (q + 1) → (Fin n → ℝ) → (Fin n → ℝ))
    (p : ℝ≥0∞) (u : (Fin n → ℝ) → ℝ) (B : ℝ) (_hB : 0 ≤ B)
    (hwords : ∀ I : List (Fin (q + 1)), wordWeight driftWeight I = 2 →
      ∃ d : (Fin n → ℝ) → ℝ, hasWeakWordDeriv X ⊤ I u d ∧
        MemLp d p volume ∧ eLpNorm d p volume ≤ ENNReal.ofReal B)
    (Ω : Opens (Fin n → ℝ)) :
    driftSecondWeakENorm X Ω p u ≤ ENNReal.ofReal ((driftSecondWordFamily q).card * B) := by
  have hb : ∀ I : List (Fin (q + 1)), wordWeight driftWeight I = 2 →
      weakWordENorm X Ω I p u ≤ ENNReal.ofReal B := by
    intro I hI
    obtain ⟨d, hw, _, hdn⟩ := hwords I hI
    have hsub : (Ω : Set (Fin n → ℝ)) ⊆ (⊤ : Opens (Fin n → ℝ)) := subset_univ _
    have he := weakWordENorm_mono_domain X ⊤ Ω hsub I p u d hw
    rw [S.weakWordENorm_eq X ⊤ I p u d hw] at he
    simp only [Opens.coe_top, Measure.restrict_univ] at he
    exact he.trans hdn
  have hs := driftSecondWeakENorm_le_of_word_bounds X Ω p u (ENNReal.ofReal B) hb
  simpa only [ENNReal.ofReal_mul (Nat.cast_nonneg _), ENNReal.ofReal_natCast] using hs

end RothschildStein.H3

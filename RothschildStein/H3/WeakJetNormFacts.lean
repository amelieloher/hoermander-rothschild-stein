-- Copyright (c) 2026 Scott Armstrong and Amélie Loher. All rights reserved.
-- Released under Apache 2.0 license as described in the file LICENSE.
module

public import RothschildStein.S.Sobolev

set_option autoImplicit false
set_option relaxedAutoImplicit false
@[expose] public section
noncomputable section
namespace RothschildStein.H3
open Set MeasureTheory TopologicalSpace
open scoped ENNReal

/-- A Sobolev word has a finite fixed weak norm (BB Definition 2.2, p. 68). -/
theorem weakWordENorm_lt_top_of_memSobolev {n m : ℕ}
    (w : Fin m → ℕ+) (X : Fin m → (Fin n → ℝ) → (Fin n → ℝ))
    (Ω : Opens (Fin n → ℝ)) (k : ℕ) (p : ℝ≥0∞) (u : (Fin n → ℝ) → ℝ)
    (hu : memSobolevX w X Ω k p u) (I : List (Fin m)) (hI : I ∈ wordFamily w k) :
    weakWordENorm X Ω I p u < ⊤ := by
  obtain ⟨g,hg,hgp⟩ := hu.2 I hI
  rw [S.weakWordENorm_eq X Ω I p u g hg]
  exact hgp.eLpNorm_lt_top

/-- Restricting a weak word to a smaller domain does not increase its norm
(BB Definition 2.2, p. 68). -/
theorem weakWordENorm_mono_domain {n m : ℕ}
    (X : Fin m → (Fin n → ℝ) → (Fin n → ℝ))
    (Ω U : Opens (Fin n → ℝ)) (hU : (U : Set (Fin n → ℝ)) ⊆ Ω)
    (I : List (Fin m)) (p : ℝ≥0∞) (u g : (Fin n → ℝ) → ℝ)
    (hg : hasWeakWordDeriv X Ω I u g) :
    weakWordENorm X U I p u ≤ weakWordENorm X Ω I p u := by
  rw [S.weakWordENorm_eq X U I p u g (S.hasWeakWordDeriv_restrict X Ω U hU hg),
    S.weakWordENorm_eq X Ω I p u g hg]
  exact eLpNorm_mono_measure g (Measure.restrict_mono_set volume hU)

end RothschildStein.H3

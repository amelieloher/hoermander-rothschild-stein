-- Copyright (c) 2026 Scott Armstrong and Amélie Loher. All rights reserved.
-- Released under Apache 2.0 license as described in the file LICENSE.
module

public import RothschildStein.H3.CompactOperatorLp

set_option autoImplicit false
set_option relaxedAutoImplicit false
set_option backward.isDefEq.respectTransparency false
@[expose] public section
noncomputable section
open Set
open scoped BigOperators
namespace RothschildStein.H3

/-- Applying the fixed drift operator preserves smoothness. -/
theorem contDiff_sumSquaresWithDrift_compact {N q : ℕ}
    (X : Fin (q + 1) → (Fin N → ℝ) → (Fin N → ℝ))
    (hX : ∀ i, ContDiff ℝ (⊤ : ℕ∞) (X i))
    {u : (Fin N → ℝ) → ℝ} (hu : ContDiff ℝ (⊤ : ℕ∞) u) :
    ContDiff ℝ (⊤ : ℕ∞) (sumSquaresWithDrift X u) := by
  have hw (I : List (Fin (q + 1))) : ContDiff ℝ (⊤ : ℕ∞) (wordDerivative X I u) :=
    contDiffOn_univ.mp (S.contDiffOn_wordDerivative ⊤ X
      (fun i => (hX i).contDiffOn) I u hu.contDiffOn)
  rw [sumSquaresWithDrift_eq_word_sum]
  have hh := (hw [0]).add
    (ContDiff.sum (s := Finset.univ) (fun (i : Fin q) _ => hw [i.succ, i.succ]))
  convert hh using 1
  funext x
  simp only [Pi.add_apply, Finset.sum_apply]


/-- Applying the fixed drift operator preserves compact support. -/
theorem hasCompactSupport_sumSquaresWithDrift {N q : ℕ}
    (X : Fin (q + 1) → (Fin N → ℝ) → (Fin N → ℝ))
    {u : (Fin N → ℝ) → ℝ} (hu : HasCompactSupport u) :
    HasCompactSupport (sumSquaresWithDrift X u) := by
  apply hu.of_isClosed_subset (isClosed_tsupport _)
  apply closure_minimal ?_ (isClosed_tsupport _)
  intro x hx
  by_contra hn
  have hw (I : List (Fin (q + 1))) : wordDerivative X I u x = 0 :=
    image_eq_zero_of_notMem_tsupport (fun h => hn (S.tsupport_wordDerivative_subset X I u h))
  have hz : sumSquaresWithDrift X u x = 0 := by
    rw [sumSquaresWithDrift_eq_word_sum]
    simp only [Pi.add_apply, Finset.sum_apply, hw, Finset.sum_const_zero, add_zero]
  exact hx hz

end RothschildStein.H3

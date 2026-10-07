-- Copyright (c) 2026 Scott Armstrong and Amélie Loher. All rights reserved.
-- Released under Apache 2.0 license as described in the file LICENSE.
module
public import RothschildStein.G3.FiniteLieFields
public import RothschildStein.G1.JetBounds
@[expose] public section
noncomputable section
open Set TopologicalSpace
open scoped BigOperators
namespace RothschildStein.G3

theorem compact_word_jet_sum_le {a s N : ℕ} {p : Fin a → ℕ+}
    (D : FreeModelData a s p) (X : Fin a → (Fin N → ℝ) → (Fin N → ℝ))
    (f : formalSpan a s p) {x : Fin N → ℝ} {k : ℕ} {B : ℝ}
    (hb : ∀ j, ‖iteratedFDeriv ℝ k (wordBracket X (modelBasisWord D j)) x‖ ≤ B) :
    (∑ j, |D.basis.equivFun f j| *
      ‖iteratedFDeriv ℝ k (wordBracket X (modelBasisWord D j)) x‖) ≤
      (∑ j, |D.basis.equivFun f j|) * B := by
  rw [Finset.sum_mul]
  exact Finset.sum_le_sum (fun j _ =>
    mul_le_mul_of_nonneg_left (hb j) (abs_nonneg _))
end RothschildStein.G3

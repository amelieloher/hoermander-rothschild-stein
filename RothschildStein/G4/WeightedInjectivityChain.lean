-- Copyright (c) 2026 Scott Armstrong and Amélie Loher. All rights reserved.
-- Released under Apache 2.0 license as described in the file LICENSE.
module

public import RothschildStein.G4.ChartDataRestriction
public import RothschildStein.G4.FiniteTransferRadius
public import Mathlib.Data.List.Chain

@[expose] public section
set_option autoImplicit false
set_option relaxedAutoImplicit false
noncomputable section
open Set

namespace RothschildStein.G4

/-- Induction along a finite frame chain propagates actual
weighted-box injectivity through proved chart-transfer implications.
A decrease of switching radius restricts the new injective domain;
the derivative estimates remain at the preceding switching radius
(BB (9.56)–(9.57), pp. 454–458). -/
theorem weighted_chart_injectivity_along_transfers {ι : Type*} {n : ℕ}
    (w : ι → Fin n → ℕ+) (F : ι → (Fin n → ℝ) → (Fin n → ℝ))
    (ρ : ι → ℝ) (R : ι → ι → Prop) (f : ℝ → ℝ) {α : ℝ}
    (hα : 0 < α) (hα1 : α ≤ 1)
    (hf : ∀ a : ℝ, 0 < a → a ≤ 1 → 0 < f a ∧ f a ≤ 1)
    (l : List ι) (hchain : l.IsChain R)
    (hρ : ∀ B ∈ l, 0 < ρ B)
    (hscale : ∀ B C, R B C → ρ C ≤ ρ B)
    (hstep : ∀ a : ℝ, 0 < a → a ≤ 1 → ∀ B C, R B C →
      InjOn (F B) (weightedBox (w B) (a * ρ B)) →
      InjOn (F C) (weightedBox (w C) (f a * ρ B)))
    (hstart : ∀ h : 0 < l.length,
      InjOn (F l[0]) (weightedBox (w l[0]) (α * ρ l[0]))) :
    ∀ j : ℕ, ∀ h : j < l.length,
      InjOn (F l[j]) (weightedBox (w l[j]) (f^[j] α * ρ l[j])) := by
  have hi := transfer_radius_iterates_positive f hα hα1 hf
  intro j
  induction j with
  | zero => intro hj; exact hstart hj
  | succ j ih =>
      intro hj
      have hjprev : j < l.length := Nat.lt_of_succ_lt hj
      have hrel : R l[j] l[j + 1] := (List.isChain_iff_getElem.mp hchain) j hj
      have hinj := hstep (f^[j] α) (hi j).1 (hi j).2 _ _ hrel (ih hjprev)
      rw [Function.iterate_succ_apply']
      apply hinj.mono
      exact weightedBox_subset_of_radius_le _
        (mul_nonneg (hf _ (hi j).1 (hi j).2).1.le (hρ _ (List.getElem_mem hj)).le)
        (mul_le_mul_of_nonneg_left (hscale _ _ hrel) (hf _ (hi j).1 (hi j).2).1.le)

end RothschildStein.G4

-- Copyright (c) 2026 Scott Armstrong and Amélie Loher. All rights reserved.
-- Released under Apache 2.0 license as described in the file LICENSE.
module

public import RothschildStein.G4.UniformTimeOneFlow
public import RothschildStein.G4.ACFlowUniqueness
public import RothschildStein.G4.TimeOneFlow
public import RothschildStein.G4.WeightedCoefficientBounds
public import RothschildStein.G4.FirstExit
public import RothschildStein.G4.UniformWordJetBounds

@[expose] public section
set_option autoImplicit false
set_option relaxedAutoImplicit false
noncomputable section
open Set
open scoped BigOperators

namespace RothschildStein.G4

/-- A mapped short-field family, possibly with repetitions, has
one numerical total value budget independent of the selected frame. -/
theorem sum_mappedShortField_norm_le {ι : Type*} [Fintype ι] {k n s : ℕ}
    {Ω K : Set (Fin n → ℝ)} (hΩ : IsOpen Ω) (hKΩ : K ⊆ Ω)
    (w : Fin (k + 1) → ℕ+) (X : Fin (k + 1) → (Fin n → ℝ) → (Fin n → ℝ))
    (hX : ∀ j, ContDiffOn ℝ (⊤ : ℕ∞) (X j) Ω) (I : ι → ShortWord w s)
    {M : ℝ} (hM : 0 ≤ M) (hjets : ∀ j, HasJetBound Ω K (X j) s M)
    {x : Fin n → ℝ} (hx : x ∈ K) :
    (∑ j : ι, ‖shortField w X (I j) x‖) ≤
      (Fintype.card ι : ℝ) * wordJetBase n 0 s M ^ s := by
  have hb : ∀ j : ι, ‖shortField w X (I j) x‖ ≤ wordJetBase n 0 s M ^ s := by
    intro j
    have hl : (I j).val.length ≤ s := (G3.length_le_weight w (I j).val).trans
      ((mem_shortWordFamily_iff w (I j).val).mp (I j).property).2
    have hj := wordBracket_jet_bound_uniform hΩ hKΩ X hX (h := 0) hM
      (fun u => by simpa only [zero_add] using hjets u) (I j).val hl
    simpa [shortField] using hj 0 (Nat.zero_le _) x hx
  calc
    _ ≤ ∑ _ : ι, wordJetBase n 0 s M ^ s := Finset.sum_le_sum (fun j _ => hb j)
    _ = _ := by simp only [Finset.sum_const, Finset.card_univ, nsmul_eq_mul]

/-- Every member of a mapped short-field family has the same
finite-jet budget, using primitive jets only through h+s. -/
theorem mappedShortField_jet_bound {ι : Type*} {k n s h : ℕ}
    {Ω K : Set (Fin n → ℝ)} (hΩ : IsOpen Ω) (hKΩ : K ⊆ Ω)
    (w : Fin (k + 1) → ℕ+) (X : Fin (k + 1) → (Fin n → ℝ) → (Fin n → ℝ))
    (hX : ∀ j, ContDiffOn ℝ (⊤ : ℕ∞) (X j) Ω) (I : ι → ShortWord w s)
    {M : ℝ} (hM : 0 ≤ M) (hjets : ∀ j, HasJetBound Ω K (X j) (h + s) M)
    (i : ι) : HasJetBound Ω K (shortField w X (I i)) h (wordJetBase n h s M ^ s) := by
  have hl : (I i).val.length ≤ s := (G3.length_le_weight w (I i).val).trans
    ((mem_shortWordFamily_iff w (I i).val).mp (I i).property).2
  exact wordBracket_jet_bound_uniform hΩ hKΩ X hX hM hjets (I i).val hl

end RothschildStein.G4

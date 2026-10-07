-- Copyright (c) 2026 Scott Armstrong and Amélie Loher. All rights reserved.
-- Released under Apache 2.0 license as described in the file LICENSE.
module

public import RothschildStein.G1.LocalStep
public import Mathlib.Analysis.Normed.Group.Bounded

@[expose] public section
set_option autoImplicit false
set_option relaxedAutoImplicit false
noncomputable section
open Set
open scoped BigOperators

namespace RothschildStein.G1

/-- Every finite collection of coefficient jets has a finite uniform bound
on a compact buffer (BB Convention 1.26, pp. 13–14).
The derivatives are within the original open domain, where they agree with
ambient derivatives. Operator norm bounds dominate all coordinate partials. -/
theorem exists_uniform_coefficient_jet_bound {m N : ℕ} {Ω K : Set (Fin N → ℝ)}
    (hΩ : IsOpen Ω) (hK : IsCompact K) (hKΩ : K ⊆ Ω)
    (X : Fin m → (Fin N → ℝ) → (Fin N → ℝ))
    (hX : ∀ i, ContDiffOn ℝ (⊤ : ℕ∞) (X i) Ω) (h : ℕ) :
    ∃ B : ℝ, 0 < B ∧ ∀ i (j : ℕ), j ≤ h → ∀ x ∈ K,
      ‖iteratedFDerivWithin ℝ j (X i) Ω x‖ ≤ B := by
  classical
  have hex : ∀ i : Fin m, ∀ j : Fin (h + 1), ∃ B : ℝ, ∀ x ∈ K,
      ‖iteratedFDerivWithin ℝ j.val (X i) Ω x‖ ≤ B := by
    intro i j
    have hc := (hX i).continuousOn_iteratedFDerivWithin
      (m := j.val) (by simp) hΩ.uniqueDiffOn
    obtain ⟨B, hB⟩ := (hK.image_of_continuousOn (hc.mono hKΩ)).isBounded.exists_norm_le
    exact ⟨B, fun x hx => hB _ (mem_image_of_mem _ hx)⟩
  choose B hB using hex
  let C := 1 + ∑ i : Fin m, ∑ j : Fin (h + 1), |B i j|
  have hsum : 0 ≤ ∑ i : Fin m, ∑ j : Fin (h + 1), |B i j| := by positivity
  refine ⟨C, by dsimp [C]; linarith, ?_⟩
  intro i j hj x hx
  let j' : Fin (h + 1) := ⟨j, Nat.lt_succ_of_le hj⟩
  have h₁ : |B i j'| ≤ ∑ k : Fin (h + 1), |B i k| :=
    Finset.single_le_sum (fun k _ => abs_nonneg (B i k)) (Finset.mem_univ j')
  have h₂ : (∑ k : Fin (h + 1), |B i k|) ≤ ∑ l : Fin m, ∑ k : Fin (h + 1), |B l k| :=
    Finset.single_le_sum (fun l _ => Finset.sum_nonneg (fun k _ => abs_nonneg (B l k)))
      (Finset.mem_univ i)
  have hb := hB i j' x hx
  have hba := le_abs_self (B i j')
  dsimp [C]
  exact (hb.trans hba |>.trans h₁ |>.trans h₂).trans (by linarith)

end RothschildStein.G1

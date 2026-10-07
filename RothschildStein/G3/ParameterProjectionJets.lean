-- Copyright (c) 2026 Scott Armstrong and Amélie Loher. All rights reserved.
-- Released under Apache 2.0 license as described in the file LICENSE.
module
public import RothschildStein.G3.BracketJetBounds
public import Mathlib.Analysis.Calculus.ContDiff.Basic
@[expose] public section
noncomputable section
open Set
open scoped BigOperators
namespace RothschildStein.G3

theorem norm_snd_pullback_jet_le
    {P E F : Type*} [NormedAddCommGroup P] [NormedSpace ℝ P]
    [NormedAddCommGroup E] [NormedSpace ℝ E]
    [NormedAddCommGroup F] [NormedSpace ℝ F]
    {Ω : Set E} (hΩ : IsOpen Ω) {Y : E → F}
    (hY : ContDiffOn ℝ (⊤ : ℕ∞) Y Ω) (n : ℕ)
    (q : P × E) (hq : q.2 ∈ Ω) :
    ‖iteratedFDeriv ℝ n (fun z : P × E => Y z.2) q‖ ≤
      ‖iteratedFDeriv ℝ n Y q.2‖ := by
  let L := ContinuousLinearMap.snd ℝ P E
  have hpre : IsOpen (L ⁻¹' Ω) := hΩ.preimage L.continuous
  have he := L.iteratedFDerivWithin_comp_right hY hΩ.uniqueDiffOn hpre.uniqueDiffOn hq
    (i := n) (by simp)
  rw [iteratedFDerivWithin_of_isOpen n hpre hq] at he
  change iteratedFDeriv ℝ n (Y ∘ L) q =
    (iteratedFDerivWithin ℝ n Y Ω q.2).compContinuousLinearMap (fun _ => L) at he
  rw [iteratedFDerivWithin_of_isOpen n hΩ hq] at he
  change ‖iteratedFDeriv ℝ n (Y ∘ L) q‖ ≤ _
  rw [he]
  apply ((iteratedFDeriv ℝ n Y q.2).norm_compContinuousLinearMap_le (fun _ => L)).trans
  have hp : (∏ _ : Fin n, ‖L‖) ≤ 1 :=
    Finset.prod_le_one₀ (fun _ _ => norm_nonneg _) (fun _ _ => ContinuousLinearMap.norm_snd_le ℝ P E)
  exact mul_le_of_le_one_right (norm_nonneg _) hp
end RothschildStein.G3

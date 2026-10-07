-- Copyright (c) 2026 Scott Armstrong and Amélie Loher. All rights reserved.
-- Released under Apache 2.0 license as described in the file LICENSE.
module
public import RothschildStein.G3.UniformCentreFlowBounds
@[expose] public section
noncomputable section
open Set
open scoped BigOperators
namespace RothschildStein.G3

/-- A finite ambient jet bound for a fixed smooth map on a compact set. -/
theorem exists_compact_ambient_jet_bound {E F : Type*}
    [NormedAddCommGroup E] [NormedSpace ℝ E]
    [NormedAddCommGroup F] [NormedSpace ℝ F]
    (f : E → F) (hf : ContDiff ℝ (⊤ : ℕ∞) f) {K : Set E} (hK : IsCompact K) (Q : ℕ) :
    ∃ C : ℝ, 0 < C ∧ ∀ k ≤ Q, ∀ x ∈ K, ‖iteratedFDeriv ℝ k f x‖ ≤ C := by
  classical
  have hex : ∀ k : Fin (Q+1), ∃ B : ℝ, ∀ x ∈ K, ‖iteratedFDeriv ℝ k.val f x‖ ≤ B := by
    intro k
    have hc := hf.continuous_iteratedFDeriv (m := k.val) (by simp)
    obtain ⟨B,hB⟩ := (hK.image hc).isBounded.exists_norm_le
    exact ⟨B,fun x hx => hB _ (mem_image_of_mem _ hx)⟩
  choose B hB using hex
  let C := 1+∑ k : Fin (Q+1), |B k|
  have hsum : 0 ≤ ∑ k : Fin (Q+1), |B k| := by positivity
  refine ⟨C,by dsimp [C]; linarith,?_⟩
  intro k hk x hx
  let k' : Fin (Q+1) := ⟨k,by omega⟩
  have he := hB k' x hx
  have hs : |B k'| ≤ ∑ j : Fin (Q+1), |B j| :=
    Finset.single_le_sum (fun j _ => abs_nonneg (B j)) (Finset.mem_univ k')
  exact ((he.trans (le_abs_self _)).trans hs).trans (by dsimp [C]; linarith)
end RothschildStein.G3

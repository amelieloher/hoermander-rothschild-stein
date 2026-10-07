-- Copyright (c) 2026 Scott Armstrong and Amélie Loher. All rights reserved.
-- Released under Apache 2.0 license as described in the file LICENSE.
module
public import RothschildStein.G4.FiniteJetBounds
public import Mathlib.Topology.MetricSpace.Bounded
@[expose] public section
set_option autoImplicit false
set_option relaxedAutoImplicit false
noncomputable section
open Set
open scoped BigOperators
namespace RothschildStein.G4

/-- Joint spatial-jet continuity supplies one finite primitive
jet budget over the compact parameter/spatial product. -/
theorem exists_compact_parameter_jet_budget {P : Type*}
    [TopologicalSpace P] [CompactSpace P] {m n : ℕ}
    {Ω K : Set (Fin n → ℝ)} (hΩ : IsOpen Ω) (hK : IsCompact K) (hKΩ : K ⊆ Ω)
    (X : P → Fin m → (Fin n → ℝ) → (Fin n → ℝ)) (H : ℕ)
    (hj : ∀ i, ∀ j ≤ H, ContinuousOn
      (fun q : P × (Fin n → ℝ) => iteratedFDeriv ℝ j (X q.1 i) q.2) (univ ×ˢ Ω)) :
    ∃ M : ℝ, 0 < M ∧ ∀ σ i, HasJetBound Ω K (X σ i) H M := by
  classical
  have hex : ∀ i : Fin m, ∀ j : Fin (H+1), ∃ L : ℝ,
      ∀ σ, ∀ y ∈ K, ‖iteratedFDeriv ℝ j.val (X σ i) y‖ ≤ L := by
    intro i j
    have hc := (hj i j.val (by omega)).mono
      (show (univ ×ˢ K : Set (P × (Fin n → ℝ))) ⊆ univ ×ˢ Ω from
        fun q hq => ⟨hq.1,hKΩ hq.2⟩)
    obtain ⟨L,hL⟩ := ((isCompact_univ.prod hK).image_of_continuousOn hc).isBounded.exists_norm_le
    exact ⟨L,fun σ y hy => hL _ (mem_image_of_mem _ (show (σ,y) ∈ (univ ×ˢ K : Set (P × (Fin n → ℝ))) from ⟨mem_univ σ,hy⟩))⟩
  choose L hL using hex
  let M := 1 + ∑ i : Fin m, ∑ j : Fin (H+1), |L i j|
  refine ⟨M,by dsimp [M]; positivity,?_⟩
  intro σ i j hj y hy
  let j' : Fin (H+1) := ⟨j,by omega⟩
  have hi : |L i j'| ≤ ∑ a : Fin (H+1), |L i a| :=
    Finset.single_le_sum (fun a _ => abs_nonneg (L i a)) (Finset.mem_univ j')
  have hk : (∑ a : Fin (H+1), |L i a|) ≤ ∑ b : Fin m, ∑ a : Fin (H+1), |L b a| :=
    Finset.single_le_sum (fun b _ => Finset.sum_nonneg (fun a _ => abs_nonneg (L b a)))
      (Finset.mem_univ i)
  rw [iteratedFDerivWithin_of_isOpen j hΩ (hKΩ hy)]
  exact ((hL i j' σ y hy).trans (le_abs_self _)).trans
    (hi.trans (hk.trans (by dsimp [M]; linarith)))
end RothschildStein.G4

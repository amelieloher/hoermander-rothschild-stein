-- Copyright (c) 2026 Scott Armstrong and Amélie Loher. All rights reserved.
-- Released under Apache 2.0 license as described in the file LICENSE.
module
public import RothschildStein.G4.JointFrameDeterminantContinuity
public import Mathlib.Topology.Order.Compact
@[expose] public section
set_option autoImplicit false
set_option relaxedAutoImplicit false
noncomputable section
open Set
open scoped BigOperators
namespace RothschildStein.G4

/-- Compact external parameters and a compact spatial buffer give
one positive maximum-frame determinant floor for the entire product. -/
theorem exists_compact_parameter_rank_floor {P ι : Type*}
    [TopologicalSpace P] [CompactSpace P] [Fintype ι] {n : ℕ}
    {K : Set (Fin n → ℝ)} (hK : IsCompact K)
    (Z : P → ι → (Fin n → ℝ) → (Fin n → ℝ))
    (hZ : ∀ j, ContinuousOn (fun q : P × (Fin n → ℝ) => Z q.1 j q.2) (univ ×ˢ K))
    (hspan : ∀ σ, ∀ y ∈ K, ∃ B : Fin n → ι, frameDet (Z σ) B y ≠ 0) :
    ∃ Δ : ℝ, 0 < Δ ∧ ∀ σ, ∀ y ∈ K, ∃ B : Fin n → ι,
      Δ ≤ |frameDet (Z σ) B y| := by
  classical
  let T : Set (P × (Fin n → ℝ)) := univ ×ˢ K
  have hT : IsCompact T := isCompact_univ.prod hK
  rcases T.eq_empty_or_nonempty with he | hne
  · refine ⟨1,by norm_num,?_⟩
    intro σ y hy
    have hh : (σ,y) ∈ T := ⟨mem_univ _,hy⟩
    simp only [he,mem_empty_iff_false] at hh
  let f := fun q : P × (Fin n → ℝ) => ∑ B : Fin n → ι, |frameDet (Z q.1) B q.2|
  have hf : ContinuousOn f T :=
    continuousOn_finsetSum _ (fun B _ => (frameDet_joint_continuousOn Z hZ B).abs)
  have hfpos : ∀ q ∈ T, 0 < f q := by
    intro q hq
    obtain ⟨B,hB⟩ := hspan q.1 q.2 hq.2
    exact (abs_pos.mpr hB).trans_le
      (Finset.single_le_sum (fun C _ => abs_nonneg (frameDet (Z q.1) C q.2)) (Finset.mem_univ B))
  obtain ⟨q,hq,hmin⟩ := hT.exists_isMinOn hne hf
  obtain ⟨B₀,_⟩ := hspan q.1 q.2 hq.2
  have hcard : (0 : ℝ) < Fintype.card (Fin n → ι) := by
    exact_mod_cast Fintype.card_pos_iff.mpr ⟨B₀⟩
  refine ⟨f q / Fintype.card (Fin n → ι),div_pos (hfpos q hq) hcard,?_⟩
  intro σ y hy
  obtain ⟨B,_,hB⟩ := Finset.exists_max_image (Finset.univ : Finset (Fin n → ι))
    (fun B => |frameDet (Z σ) B y|) ⟨B₀,Finset.mem_univ _⟩
  refine ⟨B,?_⟩
  apply (div_le_iff₀ hcard).mpr
  have hs : f (σ,y) ≤ (Fintype.card (Fin n → ι) : ℝ)*|frameDet (Z σ) B y| := by
    calc
      _ ≤ ∑ _C : Fin n → ι, |frameDet (Z σ) B y| :=
        Finset.sum_le_sum (fun C hC => hB C hC)
      _ = _ := by simp
  exact (hmin ⟨mem_univ _,hy⟩).trans (by simpa only [mul_comm] using hs)
end RothschildStein.G4

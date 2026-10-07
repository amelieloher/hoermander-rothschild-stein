-- Copyright (c) 2026 Scott Armstrong and Amélie Loher. All rights reserved.
-- Released under Apache 2.0 license as described in the file LICENSE.
module

public import RothschildStein.S.HolderBounds
public import RothschildStein.S.Sobolev
public import RothschildStein.Definitions.memHolderX
public import RothschildStein.Definitions.holderXENorm

set_option autoImplicit false
set_option relaxedAutoImplicit false
set_option backward.isDefEq.respectTransparency false
@[expose] public section
noncomputable section
open Set TopologicalSpace
open scoped ENNReal BigOperators
namespace RothschildStein.S
variable {n q : ℕ}

/-- The zero-order weighted word family consists exactly of
the empty word (BB Def 2.13, p. 81; drift has positive weight). -/
theorem wordFamily_zero (w : Fin q → ℕ+) : wordFamily w 0 = {[]} := by
  classical
  ext I
  rw [mem_wordFamily_iff,Finset.mem_singleton]
  constructor
  · intro h
    have hl := length_le_wordWeight w I
    exact List.length_eq_zero_iff.mp (by omega)
  · intro h
    subst I
    simp only [wordWeight,List.map_nil,List.sum_nil,le_refl]

/-- The empty intrinsic derivative has exactly the
pointwise Hölder norm of the input (BB Def 2.13, p. 81). -/
theorem intrinsicWordENorm_nil
    (X : Fin q → (Fin n → ℝ) → (Fin n → ℝ))
    (d : (Fin n → ℝ) → (Fin n → ℝ) → ℝ≥0∞) (Ω : Opens (Fin n → ℝ))
    (α : ℝ) (f : (Fin n → ℝ) → ℝ) :
    intrinsicWordENorm X d Ω [] α f = holderENorm d α (Ω : Set (Fin n → ℝ)) f := by
  have hs : {r | ∃ g : (Fin n → ℝ) → ℝ, hasIntrinsicWordDeriv X Ω [] f g ∧
      r = holderENorm d α (Ω : Set (Fin n → ℝ)) g} =
      {holderENorm d α (Ω : Set (Fin n → ℝ)) f} := by
    ext r
    constructor
    · rintro ⟨g,hg,rfl⟩
      exact (holderENorm_congr d α (Ω : Set (Fin n → ℝ)) g hg).symm ▸ mem_singleton _
    · intro hr
      exact ⟨f,fun _ _ => rfl,mem_singleton_iff.mp hr⟩
  unfold intrinsicWordENorm
  rw [hs,sInf_singleton]

/-- Zero-order membership in the intrinsic class is
exactly finiteness of the pointwise Hölder norm (BB Def 2.13, p. 81). -/
theorem memHolderX_zero_iff (w : Fin q → ℕ+)
    (X : Fin q → (Fin n → ℝ) → (Fin n → ℝ))
    (d : (Fin n → ℝ) → (Fin n → ℝ) → ℝ≥0∞) (Ω : Opens (Fin n → ℝ))
    (α : ℝ) (f : (Fin n → ℝ) → ℝ) :
    memHolderX w X d Ω 0 α f ↔ holderENorm d α (Ω : Set (Fin n → ℝ)) f < ⊤ := by
  constructor
  · exact fun h => h.1
  · intro h
    refine ⟨h,fun I hI => ?_⟩
    rw [wordFamily_zero,Finset.mem_singleton] at hI
    subst I
    exact ⟨f,fun _ _ => rfl,h⟩

/-- The zero-order intrinsic norm equals its scalar
Hölder norm (BB Def 2.13, p. 81). -/
theorem holderXENorm_zero (w : Fin q → ℕ+)
    (X : Fin q → (Fin n → ℝ) → (Fin n → ℝ))
    (d : (Fin n → ℝ) → (Fin n → ℝ) → ℝ≥0∞) (Ω : Opens (Fin n → ℝ))
    (α : ℝ) (f : (Fin n → ℝ) → ℝ) :
    holderXENorm w X d Ω 0 α f = holderENorm d α (Ω : Set (Fin n → ℝ)) f := by
  classical
  simp only [holderXENorm,wordFamily_zero,Finset.sum_singleton,intrinsicWordENorm_nil]

end RothschildStein.S

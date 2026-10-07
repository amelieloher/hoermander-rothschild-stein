-- Copyright (c) 2026 Scott Armstrong and Amélie Loher. All rights reserved.
-- Released under Apache 2.0 license as described in the file LICENSE.
module

public import RothschildStein.S.IntrinsicUniqueness
public import RothschildStein.S.HolderBounds
public import RothschildStein.Definitions.intrinsicWordENorm

set_option autoImplicit false
set_option relaxedAutoImplicit false
@[expose] public section
noncomputable section
open Set TopologicalSpace
open scoped ENNReal
namespace RothschildStein.S
variable {n q : ℕ}

/-- Every intrinsic word representative realizes the
exact intrinsic infimum norm. Pointwise uniqueness identifies
all competitors on the domain (BB Def 2.13, p. 81; infimum). -/
theorem intrinsicWordENorm_eq_representative
    (Ω : Opens (Fin n → ℝ))
    (X : Fin q → (Fin n → ℝ) → (Fin n → ℝ))
    (d : (Fin n → ℝ) → (Fin n → ℝ) → ℝ≥0∞)
    (I : List (Fin q)) (α : ℝ) (f g : (Fin n → ℝ) → ℝ)
    (hg : hasIntrinsicWordDeriv X Ω I f g) :
    intrinsicWordENorm X d Ω I α f = holderENorm d α (Ω : Set (Fin n → ℝ)) g := by
  unfold intrinsicWordENorm
  have he : {r | ∃ h : (Fin n → ℝ) → ℝ,hasIntrinsicWordDeriv X Ω I f h ∧
      r = holderENorm d α (Ω : Set (Fin n → ℝ)) h} =
      {holderENorm d α (Ω : Set (Fin n → ℝ)) g} := by
    ext r
    constructor
    · rintro ⟨h,hh,rfl⟩
      exact Set.mem_singleton_iff.mpr (holderENorm_congr d α (Ω : Set (Fin n → ℝ)) h
        (hasIntrinsicWordDeriv_unique Ω X I hh hg))
    · intro hr
      exact ⟨g,hg,Set.mem_singleton_iff.mp hr⟩
  rw [he,sInf_singleton]

end RothschildStein.S

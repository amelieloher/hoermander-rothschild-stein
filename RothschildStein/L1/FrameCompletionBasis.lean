-- Copyright (c) 2026 Scott Armstrong and Amélie Loher. All rights reserved.
-- Released under Apache 2.0 license as described in the file LICENSE.
module

public import Mathlib.Basic.Real.Basic
public import Mathlib.LinearAlgebra.Basis.VectorSpace
public import Mathlib.LinearAlgebra.FiniteDimensional.Defs

@[expose] public section
set_option autoImplicit false
set_option relaxedAutoImplicit false
noncomputable section
open Set Module

namespace RothschildStein.L1

/-- A prescribed independent family can be completed using only
vectors from the prescribed spanning family (BB pp. 519–520). -/
theorem exists_basis_in_range_extending {ι : Type*} {n N : ℕ}
    (Z : ι → (Fin N → ℝ)) (v : Fin n → (Fin N → ℝ))
    (hv : LinearIndependent ℝ v) (hspan : Submodule.span ℝ (Set.range Z) = ⊤)
    (hmem : ∀ j, v j ∈ Set.range Z) :
    ∃ S : Set (Fin N → ℝ), ∃ b : Basis (Fin n ⊕ S) ℝ (Fin N → ℝ),
      (∀ j, b (Sum.inl j) = v j) ∧ ∀ k, b k ∈ Set.range Z := by
  classical
  let s := Set.range v
  have hs : LinearIndepOn ℝ id s := hv.linearIndepOn_id
  have hst : s ⊆ Set.range Z := by rintro _ ⟨j, rfl⟩; exact hmem j
  have ht : ⊤ ≤ Submodule.span ℝ (Set.range Z) := by rw [hspan]
  let T := hs.extend hst
  let S := T \ s
  let b₀ := Basis.extendLe hs hst ht
  let e₀ : Fin n ≃ s := Equiv.ofInjective v hv.injective
  let e : Fin n ⊕ S ≃ T :=
    (Equiv.sumCongr e₀ (Equiv.refl S)).trans (Equiv.Set.sumDiffSubset (hs.subset_extend hst))
  let b := b₀.reindex e.symm
  have hb (k : Fin n ⊕ S) : b k = (e k).val := by
    simp [b, b₀, Basis.reindex_apply, Basis.extendLe_apply_self]
  refine ⟨S, b, ?_, ?_⟩
  · intro j
    rw [hb]
    rfl
  · intro k
    rw [hb]
    exact hs.extend_subset hst (e k).property

end RothschildStein.L1

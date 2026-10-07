-- Copyright (c) 2026 Scott Armstrong and Amélie Loher. All rights reserved.
-- Released under Apache 2.0 license as described in the file LICENSE.
module

public import RothschildStein.L1.FrameCompletionBasis
public import RothschildStein.L1.FrameIndependence
public import Mathlib.LinearAlgebra.Dimension.StrongRankCondition
public import Mathlib.LinearAlgebra.Matrix.Nonsingular
public import Mathlib.Data.Fintype.EquivFin

@[expose] public section
set_option autoImplicit false
set_option relaxedAutoImplicit false
noncomputable section
open Set Module

namespace RothschildStein.L1

/-- Complete the prescribed independent field values to a genuine
nonzero frame, preserving the original indices in its first block. -/
theorem exists_fin_basis_completion {ι : Type*} {n m : ℕ}
    (Z : ι → (Fin (n + m) → ℝ) → (Fin (n + m) → ℝ))
    (ξ : Fin (n + m) → ℝ) (B : Fin n → ι)
    (hB : LinearIndependent ℝ (fun j => Z (B j) ξ))
    (hspan : Submodule.span ℝ (Set.range (fun I => Z I ξ)) = ⊤) :
    ∃ bFin : Basis (Fin (n + m)) ℝ (Fin (n + m) → ℝ),
      (∀ j, bFin (Fin.castAdd m j) = Z (B j) ξ) ∧
      (∀ j, bFin (Fin.natAdd n j) ∈ Set.range (fun I => Z I ξ)) := by
  classical
  obtain ⟨S, b, hb, hrange⟩ := exists_basis_in_range_extending
    (fun I => Z I ξ) (fun j => Z (B j) ξ) hB hspan (fun j => ⟨B j, rfl⟩)
  let frameCompletionSumFinite : Finite (Fin n ⊕ S) := Module.Finite.finite_basis b
  let frameCompletionFiberFinite : Finite S :=
    Finite.of_injective (Sum.inr : S → Fin n ⊕ S) Sum.inr_injective
  let frameCompletionFiberFintype : Fintype S := Fintype.ofFinite S
  have hcard : Fintype.card S = m := by
    have hh : n + m = n + Fintype.card S := by
      simpa using Module.finrank_eq_card_basis b
    omega
  let eS : S ≃ Fin m := Fintype.equivOfCardEq (by simpa using hcard)
  let e : Fin n ⊕ S ≃ Fin (n + m) :=
    (Equiv.sumCongr (Equiv.refl (Fin n)) eS).trans finSumFinEquiv
  let bFin := b.reindex e
  have hbFin (j : Fin n) : bFin (Fin.castAdd m j) = Z (B j) ξ := by
    have he : e (Sum.inl j) = Fin.castAdd m j := rfl
    rw [← he]
    simpa only [bFin, Basis.reindex_apply, Equiv.symm_apply_apply] using hb j
  have hmem (j : Fin m) : bFin (Fin.natAdd n j) ∈ Set.range (fun I => Z I ξ) := by
    simpa only [bFin, Basis.reindex_apply] using hrange (e.symm (Fin.natAdd n j))
  exact ⟨bFin, hbFin, hmem⟩

/-- Basis values in the two coordinate blocks certify the
nonzero determinant of their joined field frame. -/
theorem frameDet_ne_zero_of_basis_blocks {ι : Type*} {n m : ℕ}
    (Z : ι → (Fin (n + m) → ℝ) → (Fin (n + m) → ℝ))
    (ξ : Fin (n + m) → ℝ) (B : Fin n → ι) (C : Fin m → ι)
    (b : Basis (Fin (n + m)) ℝ (Fin (n + m) → ℝ))
    (hB : ∀ j, b (Fin.castAdd m j) = Z (B j) ξ)
    (hC : ∀ j, Z (C j) ξ = b (Fin.natAdd n j)) :
    G4.frameDet Z (Fin.addCases B C) ξ ≠ 0 := by
  have heq : (fun j => Z (Fin.addCases B C j) ξ) = b := by
    funext j
    refine Fin.addCases ?_ ?_ j
    · intro i
      simpa only [Fin.addCases_left] using (hB i).symm
    · intro i
      simpa only [Fin.addCases_right] using hC i
  apply (frameDet_ne_zero_iff_linearIndependent Z (Fin.addCases B C) ξ).mpr
  rw [heq]
  exact b.linearIndependent

/-- Complete the original indices in the first block using
only indices from the actual spanning field family. -/
theorem exists_frame_completion {ι : Type*} {n m : ℕ}
    (Z : ι → (Fin (n + m) → ℝ) → (Fin (n + m) → ℝ))
    (ξ : Fin (n + m) → ℝ) (B : Fin n → ι)
    (hB : LinearIndependent ℝ (fun j => Z (B j) ξ))
    (hspan : Submodule.span ℝ (Set.range (fun I => Z I ξ)) = ⊤) :
    ∃ C : Fin m → ι, G4.frameDet Z (Fin.addCases B C) ξ ≠ 0 := by
  classical
  obtain ⟨bFin, hbFin, hmem⟩ := exists_fin_basis_completion Z ξ B hB hspan
  choose C hC using hmem
  exact ⟨C, frameDet_ne_zero_of_basis_blocks Z ξ B C bFin hbFin hC⟩

end RothschildStein.L1

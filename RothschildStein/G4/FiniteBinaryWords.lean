-- Copyright (c) 2026 Scott Armstrong and Amélie Loher. All rights reserved.
-- Released under Apache 2.0 license as described in the file LICENSE.
module

public import RothschildStein.G4.CombinationJetBounds

@[expose] public section
set_option autoImplicit false
set_option relaxedAutoImplicit false
noncomputable section
open Set Hormander.C
open scoped BigOperators

namespace RothschildStein.G4

/-- Height of the actual binary bracket expression. -/
def binaryWordHeight {k : ℕ} : Hormander.Interface.LieWord k → ℕ
  | .generator _ => 1
  | .bracket u v => max (binaryWordHeight u) (binaryWordHeight v) + 1

/-- Finite carrier of all binary expressions up to a height bound.
This carrier is purely combinatorial and contains no actual vector fields. -/
def finiteBinaryWords (k : ℕ) : ℕ → Finset (Hormander.Interface.LieWord k)
  | 0 => ∅
  | H + 1 => by
    classical
    exact (Finset.univ.image Hormander.Interface.LieWord.generator) ∪
      ((finiteBinaryWords k H ×ˢ finiteBinaryWords k H).image
        (fun uv => Hormander.Interface.LieWord.bracket uv.1 uv.2))

/-- Every expression satisfying the height bound belongs to the
finite combinatorial carrier. -/
theorem mem_finiteBinaryWords {k H : ℕ} (u : Hormander.Interface.LieWord k)
    (hu : binaryWordHeight u ≤ H) : u ∈ finiteBinaryWords k H := by
  classical
  induction H generalizing u with
  | zero => cases u <;> simp [binaryWordHeight] at hu
  | succ H ih =>
    cases u with
    | generator i => exact Finset.mem_union_left _ (Finset.mem_image.mpr ⟨i, Finset.mem_univ _, rfl⟩)
    | bracket u v =>
      have hu' : binaryWordHeight u ≤ H := by simp only [binaryWordHeight] at hu; omega
      have hv' : binaryWordHeight v ≤ H := by simp only [binaryWordHeight] at hu; omega
      exact Finset.mem_union_right _ (Finset.mem_image.mpr ⟨(u, v),
        Finset.mem_product.mpr ⟨ih u hu', ih v hv'⟩, rfl⟩)

/-- Positive weights dominate binary height, so a weighted length
bound suffices to choose the finite carrier uniformly. -/
theorem binaryWordHeight_le_weight {k : ℕ} (w : Fin (k + 1) → ℕ+)
    (u : Hormander.Interface.LieWord k) : binaryWordHeight u ≤ G1.binaryWeight w u := by
  have hh : ∀ u : Hormander.Interface.LieWord k, 0 < binaryWordHeight u := by
    intro u
    cases u <;> simp [binaryWordHeight]
  induction u with
  | generator i => exact (w i).pos
  | bracket u v ihu ihv =>
    have hu := hh u
    have hv := hh v
    simp only [binaryWordHeight, G1.binaryWeight]
    omega

/-- One universal finite Jacobi mass budget for all binary words
with the prescribed height bound. -/
def binaryMassBudget (k H : ℕ) : ℝ :=
  1 + ∑ u ∈ finiteBinaryWords k H, combinationMass (binaryExpansion u)

/-- The Jacobi mass budget is positive. -/
theorem binaryMassBudget_pos (k H : ℕ) : 0 < binaryMassBudget k H := by
  have he : 0 ≤ ∑ u ∈ finiteBinaryWords k H, combinationMass (binaryExpansion u) :=
    Finset.sum_nonneg (fun _ _ => combinationMass_nonneg _)
  unfold binaryMassBudget
  linarith

/-- Every allowed expression has its Jacobi mass bounded by the
same combinatorial constant. -/
theorem combinationMass_le_binaryMassBudget {k H : ℕ} (w : Fin (k + 1) → ℕ+)
    (u : Hormander.Interface.LieWord k) (hu : G1.binaryWeight w u ≤ H) :
    combinationMass (binaryExpansion u) ≤ binaryMassBudget k H := by
  classical
  have he := Finset.single_le_sum (fun u _ => combinationMass_nonneg (binaryExpansion u))
    (mem_finiteBinaryWords u ((binaryWordHeight_le_weight w u).trans hu))
  unfold binaryMassBudget
  linarith

end RothschildStein.G4

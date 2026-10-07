-- Copyright (c) 2026 Scott Armstrong and Amélie Loher. All rights reserved.
-- Released under Apache 2.0 license as described in the file LICENSE.
module
public import RothschildStein.G3.HomogeneousModel
public import RothschildStein.Definitions.noDriftWeight
public import RothschildStein.Definitions.driftWeight
@[expose] public section
noncomputable section
namespace RothschildStein.G3

/-- The concrete ordered homogeneous basis data used by the two
free-model constructions (BB pp. 525–528, Theorems 10.31–10.32). -/
structure FreeModelData (a s : ℕ) (p : Fin a → ℕ+) where
  basis : Module.Basis (Fin (freeDimension a s p)) ℝ (formalSpan a s p)
  weight : Fin (freeDimension a s p) → ℕ
  dimension_pos : 0 < freeDimension a s p
  weight_pos : ∀ j, 0 < weight j
  weight_mono : Monotone weight
  weight_bound : ∀ j, weight j ≤ s
  basis_homogeneous : ∀ j, weightProjection (weight j) (basis j).val = (basis j).val
  basis_commutator : ∀ j, (basis j).val ∈ commutatorSet a s p
  contains_generators : ∀ i : Fin a, ∃ j, (basis j).val = truncatedBracket [i]

/-- The free-model basis data exist for every nonempty retained alphabet
(BB Proposition 10.48, p. 525). -/
theorem nonempty_freeModelData {a s : ℕ} (p : Fin a → ℕ+)
    (ha : 0 < a) (hp : ∀ i, (p i : ℕ) ≤ s) : Nonempty (FreeModelData a s p) := by
  obtain ⟨b, w, hm, hpos, hh, hb, hg⟩ := exists_sorted_homogeneous_basis p hp
  exact ⟨⟨b, w, freeDimension_pos_of_generator p ⟨0, ha⟩ (hp ⟨0, ha⟩),
    fun j => (hpos j).1, hm, fun j => (hpos j).2, hh, hb, hg⟩⟩

/-- The homogeneous group associated with concrete free-model data
(BB Theorems 10.31–10.32, pp. 511–512). -/
def FreeModelData.group {a s : ℕ} {p : Fin a → ℕ+} (D : FreeModelData a s p) :
    HomogeneousGroup (freeDimension a s p) :=
  homogeneousModelOfBasis D.basis D.weight D.dimension_pos D.weight_pos D.weight_mono D.basis_homogeneous

/-- Choice of concrete free-model data, with the fixed dimension
(BB pp. 525–528). -/
def freeModelData {a s : ℕ} (p : Fin a → ℕ+) (ha : 0 < a)
    (hp : ∀ i, (p i : ℕ) ≤ s) : FreeModelData a s p :=
  Classical.choice (nonempty_freeModelData p ha hp)

end RothschildStein.G3

-- Copyright (c) 2026 Scott Armstrong and Amélie Loher. All rights reserved.
-- Released under Apache 2.0 license as described in the file LICENSE.
module

public import Mathlib.Basic.NNReal.Defs
public import Mathlib.Data.Fintype.Prod
public import Mathlib.Data.Fintype.Fin
public import Mathlib.Data.Finset.Lattice.Fold
public import Mathlib.Tactic.Positivity

set_option autoImplicit false
set_option relaxedAutoImplicit false
@[expose] public section
noncomputable section
open scoped NNReal
namespace RothschildStein.H3

/-- The common coefficient max{1,max_ij(B_ij+|c_ij|)},
with the empty matrix assigned zero before the outer maximum.
BB Theorem 8.50, pp. 379–380. -/
def secondJetHolderMax {q : ℕ} (B c : Fin q → Fin q → ℝ) : ℝ :=
  max 1 ((Finset.univ : Finset (Fin q × Fin q)).sup
    (fun ij => Real.toNNReal (B ij.1 ij.2 + |c ij.1 ij.2|)) : ℝ≥0)

/-- The common coefficient is at least one. -/
theorem one_le_secondJetHolderMax {q : ℕ} (B c : Fin q → Fin q → ℝ) :
    1 ≤ secondJetHolderMax B c := le_max_left _ _

/-- Every nonnegative analytic coefficient plus its
absolute correction is bounded by the common coefficient. -/
theorem coefficient_le_secondJetHolderMax {q : ℕ} (B c : Fin q → Fin q → ℝ)
    (hB : ∀ i j, 0 ≤ B i j) (i j : Fin q) :
    B i j + |c i j| ≤ secondJetHolderMax B c := by
  have hn : 0 ≤ B i j + |c i j| := add_nonneg (hB i j) (abs_nonneg _)
  calc
    _ = (Real.toNNReal (B i j + |c i j|) : ℝ) := (Real.coe_toNNReal _ hn).symm
    _ ≤ ((Finset.univ : Finset (Fin q × Fin q)).sup
        (fun ij => Real.toNNReal (B ij.1 ij.2 + |c ij.1 ij.2|)) : ℝ≥0) :=
      NNReal.coe_le_coe.mpr (Finset.le_sup (f := fun ij : Fin q × Fin q =>
        Real.toNNReal (B ij.1 ij.2 + |c ij.1 ij.2|)) (Finset.mem_univ (i, j)))
    _ ≤ _ := le_max_right _ _

end RothschildStein.H3

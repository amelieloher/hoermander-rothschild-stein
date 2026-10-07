-- Copyright (c) 2026 Scott Armstrong and Amélie Loher. All rights reserved.
-- Released under Apache 2.0 license as described in the file LICENSE.
module

public import RothschildStein.G4.GlobalReduction

@[expose] public section
set_option autoImplicit false
set_option relaxedAutoImplicit false
noncomputable section
open Set
open scoped BigOperators

namespace RothschildStein.G4

/-- Reindexing a finite field family leaves the global denominator
unchanged; the universal model can therefore use its numerical cardinality. -/
theorem determinantSquareSum_reindex {ι κ : Type*} [Fintype ι] [Fintype κ]
    {n : ℕ} (e : κ ≃ ι) (Z : ι → (Fin n → ℝ) → (Fin n → ℝ)) (x : Fin n → ℝ) :
    determinantSquareSum (fun j => Z (e j)) x = determinantSquareSum Z x := by
  let E : (Fin n → κ) ≃ (Fin n → ι) := Equiv.arrowCongr (Equiv.refl _) e
  exact E.sum_comp (fun B => frameDet Z B x ^ 2)

/-- Reindexing a finite field family transports the actual global
reduction coefficient by the same equivalence. -/
theorem reductionCoefficient_reindex {ι κ : Type*} [Fintype ι] [Fintype κ]
    [DecidableEq ι] [DecidableEq κ] {n : ℕ} (e : κ ≃ ι)
    (Z : ι → (Fin n → ℝ) → (Fin n → ℝ))
    (V : (Fin n → ℝ) → (Fin n → ℝ)) (J : κ) :
    reductionCoefficient (fun j => Z (e j)) V J = reductionCoefficient Z V (e J) := by
  classical
  funext x
  unfold reductionCoefficient
  rw [determinantSquareSum_reindex e Z x]
  congr 1
  let E : (Fin n → κ) ≃ (Fin n → ι) := Equiv.arrowCongr (Equiv.refl _) e
  have he := E.sum_comp (fun B => ∑ i : Fin n,
    if B i = e J then frameDet Z B x * replacementDet Z B (V x) i x else 0)
  rw [← he]
  apply Finset.sum_congr rfl
  intro B hB
  apply Finset.sum_congr rfl
  intro i hi
  change (if B i = J then _ else 0) = (if e (B i) = e J then _ else 0)
  simp only [e.injective.eq_iff]
  rfl

end RothschildStein.G4

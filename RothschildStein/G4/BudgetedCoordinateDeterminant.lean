-- Copyright (c) 2026 Scott Armstrong and Amélie Loher. All rights reserved.
-- Released under Apache 2.0 license as described in the file LICENSE.
module

public import RothschildStein.G4.RelativeDeterminant
public import RothschildStein.G4.BudgetedExpansionOperations
public import RothschildStein.G4.AdditiveJetBounds

@[expose] public section
set_option autoImplicit false
set_option relaxedAutoImplicit false
noncomputable section
open Set
open scoped BigOperators

namespace RothschildStein.G4

/-- The coordinate determinant has a universal permutation-count
coefficient budget at every jet order, including dimension zero. -/
theorem coordinateDet_budget {ι : Type*} {n : ℕ} (Ω K : Set (Fin n → ℝ))
    (Z : ι → (Fin n → ℝ) → (Fin n → ℝ)) (w : ι → ℕ+) (B C : Fin n → ι) (h : ℕ) :
    HasBudgetedGeneratorExpansion Ω K Z w B n (frameWeight w B - frameWeight w C) h
      (fun x => (frameCoordinateMatrix Z B C x).det) (n.factorial : ℝ) := by
  classical
  have hsign : ∀ σ : Equiv.Perm (Fin n), |((Equiv.Perm.sign σ : ℤ) : ℝ)| = 1 := by
    intro σ
    rw [← Int.cast_abs, Equiv.Perm.sign_abs, Int.cast_one]
  have hterm : ∀ σ : Equiv.Perm (Fin n), HasBudgetedGeneratorExpansion Ω K Z w B n
      (frameWeight w B - frameWeight w C) h
      (fun x => ((Equiv.Perm.sign σ : ℤ) : ℝ) *
        ∏ j, frameCoefficient Z B (Z (C j)) (σ j) x) 1 := by
    intro σ
    exact HasBudgetedGeneratorExpansion.term _ _ 1 zero_le_one contDiffOn_const
      (by simpa only [hsign σ] using const_hasJetBound Ω K h ((Equiv.Perm.sign σ : ℤ) : ℝ))
      (coordinateDet_product_isGenerator Z w B C σ)
  have he := (budgetedExpansion_sum Finset.univ _ (fun _ => (1 : ℝ))
    (fun σ _ => hterm σ)).congr (g := fun x => (frameCoordinateMatrix Z B C x).det)
      (fun x _ => Matrix.det_apply' _)
  simpa only [Finset.sum_const, Finset.card_univ, nsmul_eq_mul, mul_one,
    Fintype.card_perm, Fintype.card_fin] using he

end RothschildStein.G4
